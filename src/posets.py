#!python3

import itertools
import networkx as nx # needed for PosetDAG

class PosetAbstract:
    """An abstract class all posets should be children of."""
    
    def __init__(self):
        self.sort_key_dict = {el : i for i, el in enumerate(self)}

    def __contains__(self, element):
        pass

    def __iter__(self):
        """Return generator yielding elements in non-increasing order."""
        pass

    def sort_key(self, element):
        """Function that gives a number to each element according to __iter__."""
        return self.sort_key_dict[element]

    def leq(self, a, b):
        """Return True if a<=b."""
        pass

    def star(self, element):
        """Return the star of the element as a set of elements."""
        pass

    def str_element(self, element):
        """Return a print-friendly string representation of a given element."""
        if element not in self:
            raise ValueError(f"The given element is not in the poset.")
        return str(element)
    
class PosetDAG(PosetAbstract):
    """A generic poset given by a directed acyclic graph"""
    def __init__(self, list_of_relations):
        self.dag = nx.DiGraph(list_of_relations)
        if nx.is_directed_acyclic_graph(self.dag):
            self.dag = nx.transitive_reduction(self.dag)
        else:
            raise ValueError(f"The inputed relations define a graph that is not acyclic.")
        self.sort_key_dict = {el : i for i, el in enumerate(self.__iter__())}

    def __contains__(self, element):
        return element in self.dag

    def __iter__(self):
        return reversed(list(nx.lexicographical_topological_sort(self.dag)))

    def sort_key(self, element):
        return self.sort_key_dict[element]

    def leq(self, a, b):
        return nx.has_path(self.dag, a, b)

    def star(self, element):
        return nx.descendants(self.dag, element) | {element}

    def str_element(self, element):
        if element not in self.dag:
            raise ValueError(f"The given element is not in the poset.")
        return str(element)

class PosetLinear(PosetAbstract):
    """Totally ordered set"""
    def __init__(self, list_of_elements):
        if len(list_of_elements)!=len(set(list_of_elements)):
            raise ValueError("There are repeated elements in the list of elements provided.")
        self.elements = list(list_of_elements)
        self.elements_indices = {el : i for i, el in enumerate(self.elements)}

    def __contains__(self, element):
        return element in self.elements 

    def __iter__(self):
        return (self.elements[i] for i in range(len(self.elements)-1,-1,-1))

    def sort_key(self, element):
        return -self.elements_indices[element]

    def leq(self, a, b):
        if a not in self:
            raise ValueError(f"The element `{a}` is not in the poset.")
        if b not in self:
            raise ValueError(f"The element `{b}` is not in the poset.")
        return self.elements_indices[a]<=self.elements_indices[b]

    def star(self, element):
        if element not in self:
            raise ValueError(f"The element `{element}` is not in the poset.")
        return set(self.elements[self.elements_indices[element]:])

class SubPoset(PosetAbstract):
    """A wrapper class restricting a poset to its subset."""
    def __init__(self, poset, subset):
        subset = set(subset)
        if all(s in poset for s in subset):
            self.poset  = poset
            self.subset = subset
        else:
            raise ValueError("Given subset is not contained in the given poset.")
        super().__init__()

    def __contains__(self, element):
        return element in self.subset

    def __iter__(self):
        """Return generator yielding elements in non-increasing order."""
        return (s for s in self.poset if s in self.subset)

    def leq(self, a, b):
        """Return True if a<=b."""
        if a in self.subset and b in self.subset:
            return self.poset.leq(a,b)
        else:
            raise ValueError(f"The elements `{a}`, `{b}` are not both in the subposet.")

    def star(self, element):
        """Return the star of the element as a set of elements."""
        return self.poset.star(element) & self.subset

class SimplicialComplex(PosetAbstract):
    """Poset of a simplicial complex."""
    def __init__(self, data):
        self.dim   = {}
        self.bnd   = {}
        self.cobnd = {}
        self._build_complex(data)
        self._add_cobnd()
        self._simple_print = True if all(len(str(el[0]))==1 for el in self.dim[0]) else False
        super().__init__()

    def __len__(self):
        return len(self.bnd)

    def __contains__(self, item):
        return item in self.bnd

    def __iter__(self):
        return (s for s in sorted(self.bnd, key=lambda x: (len(x), x), reverse=True))

    def leq(self, a, b):
        if a not in self:
            raise ValueError(f"The element `{a}` is not in the poset.")
        if b not in self:
            raise ValueError(f"The element `{b}` is not in the poset.")
        return set(a).issubset(set(b))

    def star(self, element):
        if element not in self:
            raise ValueError(f"The element `{element}` is not in the poset.")
        levels = [{element}]
        while len(levels[-1])!=0:
            levels.append(set().union(*[self.cobnd[s] for s in levels[-1]]))
        return set().union(*levels)

    def str_element(self, element):
        if element not in self:
            raise ValueError(f"The given element is not in the poset.")
        if self._simple_print:
            return ''.join(str(v) for v in element)
        else:
            return str(element)

    def _build_complex(self, data):
        if str(type(data)) in (
                "<class 'list'>", "<class 'tuple'>", "<class 'set'>",
                "<class 'numpy.ndarray'>", "<class 'dict_keys'>"):
            self._build_complex_list(data)
        elif str(type(data)) == "<class 'dict'>":
            self._build_complex_dict(data)
        else:
            raise TypeError(f"Cannot build complex from type {type(data)}.")

    def _build_complex_list(self, simplex_list):
        dim = max(len(s)-1 for s in simplex_list)
        self.dim = {d : set(tuple(sorted(s)) for s in simplex_list if len(s)-1==d) for d in range(dim+1)}
        for d in range(dim, 0, -1):
            for s in self.dim[d]:
                self.bnd[s] = set(itertools.combinations(s, d))
            self.dim[d-1] = self.dim[d-1].union(*[self.bnd[s] for s in self.dim[d]])
        for v in self.dim[0]:
            self.bnd[v] = set()

    def _build_complex_dict(self, simplex_dict):
        self._build_complex_list(simplex_dict.keys())

    def _add_cobnd(self):
        self.cobnd = { s : set() for s in self.bnd}
        for s in self.bnd:
            for t in self.bnd[s]:
                self.cobnd[t].add(s)

class PosetMappingCylinder(PosetAbstract):
    """Mapping cylinder of a monotonic map."""
    def __init__(self, poset_map):
        self.dom    = poset_map.dom
        self.codom  = poset_map.codom
        self.map    = poset_map
        super().__init__()

    def __contains__(self, element):
        el, poset = element
        if poset==0:
            return el in self.dom
        elif poset==1:
            return el in self.codom
        else:
            return False

    def __iter__(self):
        for el in self.codom:
            yield el
        for el in self.dom:
            yield el

    def leq(self, a, b):
        a_el, a_poset = a
        b_el, b_poset = b
        if a_poset==0 and b_poset==0:
            return self.dom.leq(a_el, b_el)
        elif a_poset==1 and b_poset==1:
            return self.codom.leq(a_el, b_el)
        elif a_poset==0 and b_poset==1:
            return self.codom.leq(self.map[a_el], b_el)
        else:
            return False

    def star(self, element):
        el, poset = element
        if poset==1:
            return {(e, 1) for e in self.codom.star(el)}
        elif poset==0:
            star0 = self.dom.star(el)
            star1 = self.codom.star(self.map[el])
            return {(e, 0) for e in star0} | {(e, 1) for e in star1}
        else:
            return set()

    def elements_dom(self):
        return ( self.relabel_dom_to_cylinder(s) for s in self.dom )

    def elements_codom(self):
        return ( self.relabel_codom_to_cylinder(s) for s in self.codom )

    def relabel_dom_to_cylinder(self, label):
        return (label, 0)

    def relabel_codom_to_cylinder(self, label):
        return (label, 1)

    def relabel_cylinder_to_dom(self, label):
        return label[0]

    def relabel_cylinder_to_codom(self, label):
        return label[0]

#======================================================================
#======================================================================
#======================================================================

class PosetMap:
    def __init__(self, domain, codomain, map_dict):
        if not ( isinstance(domain, PosetAbstract) and isinstance(codomain, PosetAbstract) ):
            raise TypeError("Arguments `domain` and `codomain` must be instances of `PosetAbstract`.")
        if not all(el in domain for el in map_dict):
            raise ValueError("The keys of `map_dict` must be elements of the domain.")
        if not all(el in codomain for el in map_dict.values()):
            raise ValueError("The values of `map_dict` must be elements of the codomain.")
        if not all(el in map_dict for el in domain):
            raise ValueError("All elements must be mappet somewhere.")
        self.dom      = domain
        self.codom    = codomain
        self.map_dict = map_dict

    def __getitem__(self, key):
        return self.map_dict[key]

class PosetMapConstant(PosetMap):
    """Constant map sending all elements to a point"""
    def __init__(self, domain, codomain):
        if not ( isinstance(domain, PosetAbstract) and isinstance(codomain, PosetAbstract) ):
            raise TypeError("Arguments `domain` and `codomain` must be instances of `PosetAbstract`.")
        pt, = (el for el in codomain) #get the one point in the one element poset
        self.dom   = domain
        self.codom = codomain
        self.pt    = pt

    def __getitem__(self, key):
        if key not in self.dom:
            raise ValueError(f"The element `{key}` is not in the domain of the map.")
        return self.pt

class PosetMapIdentity(PosetMap):
    def __init__(self, poset):
        if not isinstance(poset, PosetAbstract):
           raise TypeError("Argument `poset` must be an instance of `PosetAbstract`.")
        self.dom   = poset
        self.codom = poset

    def __getitem__(self, key):
        if key not in self.dom:
            raise ValueError(f"The element `{key}` is not in the domain of the map.")
        return key

class PosetMapInclusion(PosetMap):
    def __init__(self, domain, codomain):
        if not isinstance(domain, SubPoset):
            domain = SubPoset(codomain, domain)
        if domain.poset!=codomain:
            raise ValueError("The domain must be a subposet of the codomain.")
        self.dom   = domain
        self.codom = codomain

    def __getitem__(self, key):
        if key not in self.dom:
            raise ValueError(f"The element `{key}` is not in the domain of the map.")
        return key

class SimplicialMap(PosetMap):
    def __init__(self, domain, codomain, vertex_map_dict, suppress_check=False):
        """For a dictionary `vertex_map_dict` describing a vertex map between two simplicial complexes,
        return a PosetMap representing the induced map between the simplicial complexes. Vertices that
        are not given are sent identically. Check that simplices are sent to simplices is performed.
        Keyword arguments:
            suppress_check -- If True, do not perform the check that simplices are sent to simplices (default False)."""
        if not ( isinstance(domain, SimplicialComplex) and isinstance(codomain, SimplicialComplex) ):
            raise TypeError("Arguments `domain` and `codomain` must be instances of `PosetAbstract`.")
        for v in vertex_map_dict:
            if not (v,) in domain:
                raise Warning(f"The vertex `{v}` is not a vertex of the domain.")

        self.dom   = domain
        self.codom = codomain
        self.vertex_map_dict = vertex_map_dict

        if (not suppress_check) and any(self[s] not in codomain for s in domain):
            raise ValueError("Not a simplicial map -- some simplex gets sent to a non-simplex.")

    def __getitem__(self, key):
        if key not in self.dom:
            raise ValueError(f"The element `{key}` is not in the domain of the map.")
        return tuple(sorted({self.vertex_map_dict.get(v,v) for v in key}))


def main():
    pass

if __name__ == '__main__':
    main()

