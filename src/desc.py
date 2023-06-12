#!python3

# import itertools
import tabulate
import networkx as nx
import numpy as np

import linear_algebra_Z2 as linalg
from posets import PosetAbstract
from posets import PosetDAG
from posets import PosetLinear
from posets import SubPoset
from posets import SimplicialComplex
from posets import PosetMappingCylinder
from posets import PosetMap
from posets import PosetMapConstant
from posets import PosetMapIdentity
from posets import PosetMapInclusion
from posets import SimplicialMap

class LabeledMatrix:

    def __init__(self, poset):
        self.poset = poset
        self.column_labels = {}
        self.row_labels = {}
        self.matrix = {}

    def __bool__(self):
        return len(self.column_labels)>0 or len(self.row_labels)>0

    def submatrix(self, rows, columns = None, relabel = None, poset = None):
        """Return a labeled matrix with selected rows and columns.
        If no columns are given, the given rows are also used to
        select columns.
        If relabel lambda function is given, the matrix is also relabeled.
        If poset is given, returned submatrix is bound to the given poset."""
        relabel = (lambda x: x) if relabel==None else relabel
        columns = rows if columns==None else columns
        submat = LabeledMatrix(self.poset if poset==None else poset)
        submat.column_labels = {relabel(lab) : {s for s in sublabs} for lab, sublabs in self.column_labels.items() if lab in columns}
        submat.row_labels    = {relabel(lab) : {s for s in sublabs} for lab, sublabs in self.row_labels.items()    if lab in rows}
        for fulllab, row in self.matrix.items():
            lab, sublab = fulllab
            if lab in rows:
                submat.matrix[(relabel(lab), sublab)] = {(relabel(collab), colsublab) for collab, colsublab in row if collab in columns}

        return submat

    def submatrix_dict(self, rows, columns = None):
        """Return a dictionary representation of the submatrix with
        selected rows and columns.
        If no columns are given, the given rows are also used to
        select columns."""
        if columns==None:
            columns=rows
        return { row : {col for col in self.matrix[row] if col[0] in columns} for row in self.matrix if row[0] in rows }

    def set_column_labels(self, labels_dict):
        if not all(l in self.poset for l in labels_dict):
            raise ValueError("Given labels are not all in the matrix poset.")
        if len(self.column_labels)>0:
            raise Warning("Matrix already has column labels.")
        self.column_labels = {lab : {sublab for sublab in sublabs} for lab, sublabs in labels_dict}

    def add_empty_column(self, label, sublabel=None):
        sublabels = self.column_labels.get(label, set())
        if sublabel==None:
            new_sublabel = min( set(range( len(sublabels)+1 )) - sublabels )
        else:
            if sublabel in sublabels:
                raise ValueError(f"Column `({label},{sublabel})` already in matrix.")
            new_sublabel = sublabel
        self.column_labels[label] = sublabels | {new_sublabel}
        return label, new_sublabel

    def add_row(self, label, row, sublabel=None):
        sublabels = self.row_labels.get(label, set())
        if sublabel==None:
            new_sublabel = min( set(range( len(sublabels)+1 )) - sublabels )
        elif sublabel not in sublabels:
            new_sublabel = sublabel
        else:
            raise ValueError(f"Row labeled `({label},{sublabel})` already in matrix.")
        for lab, sublab in row:
            if sublab not in self.column_labels.get(lab, set()):
                raise ValueError(f"Cannot add row, colum labeled `({lab},{sublab})` not in matrix.")

        self.row_labels[label] = sublabels | {new_sublabel}
        self.matrix[(label, new_sublabel)] = row
        return label, new_sublabel

    def print_matrix(self, title="", form="short", zero_symbol="0"):
        '''Print labeled matrix
        Keyword arguments:
            title -- string to be printed in position (0,0)
            form  -- `full` or `short`, full prints labeles and sublabeles,
                        short only prints labeles. For example if we have
                        two rows labeled by pi, then full prints labels (pi,0) and (pi,1),
                        and short only prints pi for both rows. (default short)
            zero_symbol -- the symbol used for zeros (default "0")'''
        cols = [element for element in self.poset if element in self.column_labels]
        rows = [element for element in self.poset if element in self.row_labels]
        column_labels = sum([[ (collab, sublab) for sublab in sorted(self.column_labels[collab])] 
                                                for collab in cols],
                            start=[])
        table = [[title] + [(self.poset.str_element(collab), sublab) for collab,sublab in column_labels]]
        for row in rows:
            for sublab in self.row_labels[row]:
                table.append( [(self.poset.str_element(row), sublab)] +
                        [1 if col in self.matrix[(row, sublab)] else zero_symbol for col in column_labels] )
        if form=="short":
            table[0] = [table[0][0]] + [el[0] for el in table[0][1:]]
            for i in range(1,len(table)):
                table[i] = [table[i][0][0]] + table[i][1:]
        print(tabulate.tabulate(table, headers='firstrow'))

class ChainComplex:

    def __init__(self, poset):
        self.poset = poset
        self.matrices = {}

    @staticmethod
    def constant_complex_on_point():
        pt_poset = SimplicialComplex([(0,)])
        cplx = ChainComplex(pt_poset)
        cplx.add_row(-1, (0,), set())
        return cplx

    @staticmethod
    def injective_resolution_of_constant_sheaf(poset):
        k_pt = ChainComplex.constant_complex_on_point()
        return k_pt.pullback(PosetMapConstant(poset, k_pt.poset))

    def add_row(self, degree, label, row):
        if degree not in self.matrices:
            self.matrices[degree] = LabeledMatrix(self.poset)
        label, sublabel = self.matrices[degree].add_row(label, row)
        if degree+1 not in self.matrices:
            self.matrices[degree+1] = LabeledMatrix(self.poset)
        self.matrices[degree+1].add_empty_column(label=label, sublabel=sublabel)

    def generators(self):
        gen_dict = {}
        for deg, mat in sorted(self.matrices.items()):
            if mat.column_labels:
                gen_dict[deg] = { lab : len(sublabs) for lab, sublabs in mat.column_labels.items()}
        return gen_dict

    def _make_exact(self, degree, element, sorting_function=None):
        """The MakeExact routine

        Disclaimer
        ==========
        sorting_function is currently not used for anything
        """
        element_star = self.poset.star(element)
        for new_row in self._make_exact_new_rows(
                            self.matrices[degree].submatrix_dict(element_star) if degree in self.matrices else {},
                            self.matrices[degree-1].submatrix_dict(element_star) if degree-1 in self.matrices else {},
                            sorting_function):
            self.add_row(degree, element, new_row)

    def _make_exact_new_rows(self, matrix_current, matrix_previous, sorting_function=None):
        """Subroutine for MakeExact (implemented as _make_exact).
        Given eta^k(pi), eta^{k-1}(pi), return list of rows that need to be added."""
        sorting_function = (lambda x: x) if sorting_function==None else sorting_function
        R, V = linalg.reduce_matrix(matrix_previous, sorting_function)
        orthogonal_complement_of_image = [row for label, row in V.items() if len(R[label])==0]

        new = "new"
        while new in (k[0] for k in matrix_current.keys()): new+="new"
        matrix_current.update({ (new, i) : row for i,row in enumerate(orthogonal_complement_of_image) })
        R, V = linalg.reduce_matrix(matrix_current, sorting_function=lambda x: ((type(x)==tuple and len(x)>0 and x[0]==new), sorting_function(x)))

        rows_to_add = []
        for label, row in R.items():
            if len(row)>0 and (type(label)==tuple and len(label)>0 and label[0]==new):
                rows_to_add.append( R[label] )

        return rows_to_add

    def pullback(self, poset_map):
        if poset_map.codom != self.poset:
            raise ValueError("The complex poset must be the same as the domain of `poset_map`.")
        poset_cyl = PosetMappingCylinder(poset_map)
        cone_cplx = ChainComplex(poset_cyl)
        for deg, mat in sorted(self.matrices.items()):
            cone_cplx.matrices[deg-1] = mat.submatrix(rows=mat.poset, relabel=poset_cyl.relabel_codom_to_cylinder, poset=poset_cyl)

        cplx_max_degree = max(self.matrices, default=0)
        deg = min(cone_cplx.matrices, default=0)+1
        while cone_cplx.matrices.get(deg, None) or deg<cplx_max_degree:
            for element in poset_map.dom:
                cone_cplx._make_exact(deg, poset_cyl.relabel_dom_to_cylinder(element))
            deg+= 1

        pullback_cplx = ChainComplex(poset_map.dom)
        for deg, mat in sorted(cone_cplx.matrices.items()):
            submat = mat.submatrix(
                list(poset_cyl.elements_dom()),
                relabel=poset_cyl.relabel_cylinder_to_dom,
                poset=poset_map.dom)
            if submat:
                pullback_cplx.matrices[deg] = submat

        return pullback_cplx

    def pushforward(self, poset_map):
        if poset_map.dom != self.poset:
            raise ValueError("The complex poset must be the same as the domain of `poset_map`.")
        
        push_cplx = ChainComplex(poset_map.codom)
        
        relabeling_rows = {}
        for deg, mat in sorted(self.matrices.items()):
            relabeling_columns = relabeling_rows if deg-1 in self.matrices else {} #else should never happen
            relabeling_rows    = {}
            push_cplx.matrices[deg] = LabeledMatrix(push_cplx.poset)

            for new_lab, new_sublab in relabeling_columns.values():
                push_cplx.matrices[deg].add_empty_column(label=new_lab, sublabel=new_sublab)

            for lab, sublab in sorted(mat.matrix, key=lambda x: (mat.poset.sort_key(x[0]), x[1])):
                row = mat.matrix[(lab, sublab)]
                new_lab, new_sublab = push_cplx.matrices[deg].add_row(
                                        label = poset_map[lab],
                                        row   = {relabeling_columns[el] for el in row})
                relabeling_rows[(lab, sublab)] = (new_lab, new_sublab)
        return push_cplx

    def proper_pushforward(self, superposet):
        """Compute proper pushforward of complex on a subposet to a bigger poset."""
        if ((isinstance(self.poset, SubPoset) and self.poset.poset!=superposet)
                and not all(s in superposet for s in self.poset)):
            raise ValueError("The complex poset is not a subsposet of the given superposet.")

        new_cplx = ChainComplex(superposet) # copy the complex
        for deg, mat in sorted(self.matrices.items()):
            new_cplx.matrices[deg] = mat.submatrix(rows=mat.poset, poset=superposet)

        max_degree = max(new_cplx.matrices, default=0) # resolve below
        deg = min(new_cplx.matrices, default=0)+1
        while new_cplx.matrices.get(deg, None) or deg<max_degree:
            for element in superposet:
                if element not in self.poset:
                    new_cplx._make_exact(deg, element)
            deg+= 1

        return new_cplx


    def proper_pullback(self, subposet):
        """Compute proper pullback of complex to a locally closed (not checked) subposet.
        Either a SubPoset object can be inputted, or a subset of elements."""
        if not isinstance(subposet, SubPoset):
            subposet = SubPoset(self.poset, subposet)
        if subposet.poset!=self.poset:
            raise ValueError("The given subposet is not a subsposet of the complex poset.")
        subposet_elements = set(subposet)
        new_cplx = ChainComplex(subposet)
        for deg, mat in sorted(self.matrices.items()):
            new_cplx.matrices[deg] = mat.submatrix(subposet_elements, poset=subposet)
        return new_cplx

    def truncate_from_right(self, degree, minimize=True):
        """Return the truncation of the complex from the right,
        removing degrees strictly larger than the given degree."""
        truncated_complex = ChainComplex(self.poset)
        truncated_complex.matrices = {
                deg : mat.submatrix(self.poset)
                for deg, mat in sorted(self.matrices.items())
            } #copy the matrices
        max_non_zero_degree = max(truncated_complex.matrices.keys(), default=degree)
        while truncated_complex.matrices.get(degree, None) or degree <= max_non_zero_degree: # Make everything exact, starting at the cut-off degree
            for p in truncated_complex.poset:
                truncated_complex._make_exact(degree, p)
            degree += 1

        if minimize:
            return truncated_complex.minimize()
        else:
            return truncated_complex

    def truncate_from_left(self, degree, minimize=True):
        """Return the truncation of the complex from the left"""
        poset_cylinder = PosetMappingCylinder(PosetMapIdentity(self.poset))
        cone_complex = ChainComplex(poset_cylinder)
        cone_complex.matrices = { #copy matrices starting with degree d to the top of the cylinder
            deg : mat.submatrix(rows=mat.poset, relabel=poset_cylinder.relabel_codom_to_cylinder, poset=poset_cylinder)
            for deg, mat in sorted(self.matrices.items())
            if deg >= degree
        }
        if degree-1 in self.matrices:
            cone_complex.matrices[degree-1] = self.matrices[degree-1].submatrix(
                    rows=self.poset, columns=[], relabel=poset_cylinder.relabel_codom_to_cylinder, poset=poset_cylinder
            ) # create the empty matrix going from the first zero sheaf to the first non-zero
        if degree in cone_complex.matrices:
            codom_matrix_degree = {label : row for label, row in cone_complex.matrices[degree].matrix.items()} #we do this copying because we change the matrix in the loop that follows
            for label, row in codom_matrix_degree.items(): # add domain-labeled copy of the matrix in the cut-off degree
                domanin_label = poset_cylinder.relabel_dom_to_cylinder(poset_cylinder.relabel_cylinder_to_codom(label))
                cone_complex.add_row(degree, domanin_label, row)

        complex_max_degree = max(cone_complex.matrices)
        deg = degree+1
        while cone_complex.matrices.get(deg, None) or deg<complex_max_degree: # make exact in the dom-part of the poset cylinder
            for element in poset_cylinder.elements_dom():
                cone_complex._make_exact(deg, element)
            deg+= 1

        truncated_complex = ChainComplex(self.poset) # take only the (dom-part, dom-part) submatrices
        for deg, mat in sorted(cone_complex.matrices.items()):
            submat = mat.submatrix(
                list(poset_cylinder.elements_dom()),
                relabel=poset_cylinder.relabel_cylinder_to_dom,
                poset=truncated_complex.poset)
            if submat:
                truncated_complex.matrices[deg-1] = submat

        if minimize: # we might get minimal already because of the construction -- should check the argument for why pullback is minimal
            return truncated_complex.minimize()
        else:
            return truncated_complex



    def minimize(self):
        """Return minimal ChainComplex quasi-isomorphic to self.
        [Is currently implemented in a very non-optimised way: computes pullback via identity]
        """
        return self.pullback(PosetMapIdentity(self.poset))

    def hypercohomology(self):
        """Compute Betti numbers of the hypercohomology of the complex, return as dictionary."""
        rank  = {deg : linalg.rank_null_of_transpose(mat.matrix)[0] for deg, mat in self.matrices.items()}
        null  = {deg : sum(len(sublabs) for lab,sublabs in mat.column_labels.items()) - rank[deg] for deg, mat in self.matrices.items()}
        betti = {deg : null[deg] - rank.get(deg-1,0) for deg in null}

        return {deg : betti[deg] for deg in betti if betti[deg]!=0}

    def str_hypercohomology(self):
        betti = self.hypercohomology()
        if min(betti, default=0)<0:
            negative = ",".join(str(betti.get(deg,0)) for deg in range(min(betti), 0)) + "|"
        else:
            negative = ""

        return negative + ",".join(str(betti.get(deg,0)) for deg in range(0, max(2, max(betti, default=0))+1 ))

    def str_chain(self):
        generators = self.generators()
        string = ""
        last_arrow = ""
        for deg in range(min(generators, default=0), max(generators, default=-1)+1):
            string+= " + ".join(
                        f"{self.poset.str_element(gen)}^{generators[deg][gen]}"
                        for gen in sorted(generators[deg], key=self.poset.sort_key))
            last_arrow = f" --{deg if deg>=0 else f'({deg})'}--> "
            string+= last_arrow
        return string[:-len(last_arrow)]

    def shift(self, shift):
        """Shifts the complex by a given value. E.g. shift=2 will put degree 1 to degree 3."""
        self.matrices = { deg+shift : matrix for deg, matrix in self.matrices.items()}

class Sheaf:
    """A generic sheaf on a poset over Z_2.

    Defining a sheaf
    ================
    Initialise the sheaf, and the use add_matrix(start, end, matrix) for each edge (start, end) in the Hasse diagram
    of the poset over which the sheaf is defined. This both defines the poset and the sheaf maps.
    If an edge implied by transitivity, i.e. not in the Hasse diagram, is added, it will be ignored.
    The dimensions of the vector spaces are inquired from the matrices. An error is raised in the case of inconsistency.
    Once all matrices are added, the method injective_resolution computes an injective resolution of the sheaf.
    The resolution is not minimal, but can be minimized with the minimize() method of ChainComplex.

    Remarks
    =======
    The poset over which the injective resolution is defined is generated as PosetDAG. If it should be defined
    over a different representation of the same poset, it can be moved by a pushforward through a poset map
    identifying the corresponding elements.

    Disclaimer
    ==========
    The class is not optimised for performance in any way.
    """

    def __init__(self):
        self.dag = nx.DiGraph()
        self.dag_transitive_reduction = None
        self.transitive_reduction_valid = False
        self.dim = {}
        self.maps = {}

    def add_edge(self, start, end, matrix):
        matrix = np.array(matrix, dtype=int) % 2
        self.dag.add_edge(start, end)
        self.set_dimension(start, matrix.shape[1])
        self.set_dimension(end, matrix.shape[0])
        self.maps[(start, end)] = matrix
        self.transitive_reduction_valid = False # transitive reduction needs to be potentially recomputed

    def set_dimension(self, vertex, dimension):
        if vertex not in self.dim:
            self.dim[vertex] = dimension
            return True
        if self.dim[vertex] != dimension:
            raise ValueError("Matrices with conflicting dimensions are added.")

    def generate_poset(self):
        return PosetDAG(self.dag) #checks for acyclicity

    def get_dag_transitive_reduction(self):
        if not self.transitive_reduction_valid:
            self.dag_transitive_reduction = nx.transitive_reduction(self.dag)
            self.transitive_reduction_valid = True
        return self.dag_transitive_reduction

    def check_commutativity(self):
        """Return True if for every a<b all paths between a and b define the same map. Else return False.
        Note: The method is performance expensive.
        """
        dag = self.get_dag_transitive_reduction()
        for a in dag:
            for b in nx.descendants(dag, a):
                paths = list(nx.all_simple_edge_paths(dag, a, b))
                if len(paths) <= 1:
                    continue
                path_map = None
                for path in paths:
                    mat = self.maps[path[0]]
                    for edge in path[1:]:
                        mat = ( self.maps[edge] @ mat ) % 2
                    if path_map != None and path_map != mat:
                        return False
        return True

    def sheaf_map(self, a, b):
        """Return the map F(a <= b) as a numpy array. Return empty matrix if not comparable"""
        if a==b: # F(p)-->F(p) is the identity matrix
            return np.eye(self.dim[a], dtype=int)
        try:
            path = nx.shortest_path(self.get_dag_transitive_reduction(), a, b)
            path = list(zip(path[:-1],path[1:])) # path -> edge path
        except nx.NetworkXNoPath:
            return np.array([], dtype=int)
        mat = self.maps[path[0]]
        for edge in path[1:]:
            mat = ( self.maps[edge] @ mat ) % 2
        return mat

    def injective_resolution(self, check_commutativity=True, minimize=False):
        """Return an injective resolution of the sheaf. By default a commutativity check is performed, but
        this can be suppresed for performance reasons by passing `check_commutativity=False`.
        """
        if check_commutativity and not self.check_commutativity():
            raise ValueError("The inputed matrices do not define a sheaf -- a commutativity clash found.")
        cplx = ChainComplex(self.generate_poset())

        # define I_0
        for p in cplx.poset:
            for _ in range(self.dim[p]): # there is dim(F(p)) summands [p] in I_0
                cplx.add_row(-1, p, set())

        # compute cplx.matrices[0]: I_0 --> I_1 (mimics ChainComplex._makeExact)
        for p in cplx.poset:
            p_star = cplx.poset.star(p)

            # The matrix F(p) --> I_0(p) has dim(F(p)) columns and sum(dim(F(q)), p<=q) rows;
            # it comprises of a column of matrices F(p<q), one for each q>=p
            column_labels = [(p, i) for i in range(self.dim[p])]
            matrix_F_to_I0 = {}
            for q in p_star:
                npmat = self.sheaf_map(p,q)
                for i, row_sublab in enumerate(sorted(cplx.matrices[0].column_labels.get(q, set()))):
                    matrix_F_to_I0[(q,row_sublab)] = {col_lab for j, col_lab in enumerate(column_labels) if npmat[i,j]}

            for new_row in cplx._make_exact_new_rows(
                                cplx.matrices[0].submatrix_dict(p_star),
                                matrix_F_to_I0):
                cplx.add_row(0, p, new_row)

        # compute the rest of the resolution
        deg = 1
        while cplx.matrices.get(deg, None):
            for p in cplx.poset:
                cplx._make_exact(deg, p)
            deg+= 1

        if minimize:
            return cplx.minimize()
        else:
            return cplx




def main():
    print("The sample example from the paper:")

    # define simplicial complexes (given list of maximal simplices)
    sigma = SimplicialComplex([
        (0,1,3), (0,1,4), (0,3,4),
        (1,2,3), (1,2,4), (2,3,4),
        (4,5), (4,6), (5,6)])
    lambd = SimplicialComplex([
            (0,1,3), (0,1,4), (0,3,4),
            (1,2,3), (1,2,4), (2,3,4)])

    # define mappings
    # arguments: domain, codomain, vertex map (vertices not given are mapped identically)
    map_g = SimplicialMap(sigma, lambd, {5:4, 6:4})
    map_h = SimplicialMap(sigma, lambd, {5:1, 6:3})

    # compute injective resolution of k_sigma and push it forward by g and h
    cplx_sigma = ChainComplex.injective_resolution_of_constant_sheaf(sigma)
    cplx_g_push = cplx_sigma.pushforward(map_g)
    cplx_h_push = cplx_sigma.pushforward(map_h)


    # print the chain complexes
    print()
    print(f"cplx_sigma = {cplx_sigma.str_chain()}")
    print()
    print(f"cplx_g_push = {cplx_g_push.str_chain()}")
    print()
    print(f"cplx_h_push = {cplx_h_push.str_chain()}")
    print()

    # define filtration of lambd
    morse = {
        'A' : {(2,)},
        'B' : {(4,),(2,4)},
        'C' : {(3,),(2,3)},
        'D' : {(1,),(1,2)},
        'E' : {(0,),(0,3)},
        'F' : {(3,4),(2,3,4)},
        'G' : {(0,4),(0,3,4)},
        'H' : {(1,4),(1,2,4)},
        'I' : {(0,1),(0,1,4)},
        'J' : {(1,3),(1,2,3)},
        'K' : {(0,1,3)}
    }


    
    # Construct the table

    table = []

    for name, cplx in (('g', cplx_g_push), ('h', cplx_h_push)):

        row = [f"RiZ^! R{name}_*"]
        for lvl, Z in sorted(morse.items()):
            row.append( cplx.proper_pullback(Z).str_hypercohomology() )
        table.append(row)

        row = [f"Ri<^! R{name}_*"]
        for lvl in sorted(morse):
            Z = set().union(*[morse[lab] for lab in morse if lab<=lvl])
            row.append( cplx.proper_pullback(Z).str_hypercohomology() )
        table.append(row)

        row = [f"Ri>^* R{name}_*"]
        for lvl in sorted(morse):
            Z = set().union(*[morse[lab] for lab in morse if lab>=lvl])
            row.append( cplx.pullback(PosetMapInclusion(Z, cplx.poset)).str_hypercohomology() )
        table.append(row)

        # =========

        row = [f"RiZ_! RiZ^* R{name}_*"]
        for lvl, Z in sorted(morse.items()):
            row.append( cplx.pullback(PosetMapInclusion(Z, cplx.poset)).proper_pushforward(cplx.poset).str_hypercohomology() )
        table.append(row)

        row = [f"Ri<*! R{name}_*"]
        for lvl in sorted(morse):
            Z = set().union(*[morse[lab] for lab in morse if lab<=lvl])
            row.append( cplx.pullback( PosetMapInclusion(Z, cplx.poset)).str_hypercohomology() )
        table.append(row)

    for row in table:
        for i in range(len(row)):
            if row[i]  == '0,0,0':
                row[i] = '-----'

    print()
    print("The table of hypercohomologies for maps g and h as presented in Examples section of the paper:")
    print(tabulate.tabulate(
        table,
        headers=["dim H^p(-)"]+sorted(morse.keys()),
        tablefmt='grid'))

if __name__ == '__main__':
    main()

