#!python3

import itertools

def reduce_matrix(matrix, sorting_function = None):
    """Given matrix D in a row-dictionary form (key=row label, value=set of column labels),
    reduce the matrix and return R,V where R=V*D
    Keyword arguments:
        sorting_function -- lambda function for sorting rows and columns,
                            if not given, standard `sorted` and `max` is used"""
    if sorting_function==None:
        sorting_function = lambda x: x
    pivot_inverse = {}
    V = {r : {r} for r in matrix}
    R = {r : {c for c in matrix[r]} for r in matrix} #copy the matrix
    for r in sorted(R, key=sorting_function):
        pivot = min(R[r], key=sorting_function, default=None)
        while pivot!=None and pivot_inverse.get(pivot, None)!=None:
            R[r]^= R[pivot_inverse[pivot]]
            V[r]^= V[pivot_inverse[pivot]]
            pivot = min(R[r], key=sorting_function, default=None)
        if pivot!= None:
            pivot_inverse[pivot] = r

    return R, V

def rank_null_of_transpose(matrix):
    R,V = reduce_matrix(matrix)
    rank, null = 0, 0
    for row in R.values():
        if len(row)>0:
            rank+=1
        else:
            null+=1

    return rank, null

def main():
    pass

if __name__ == '__main__':
    main()

