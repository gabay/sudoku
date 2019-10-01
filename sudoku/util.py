def argmax(elements: list)# -> int:
    # return the index of the highest value in the sequence
    return elements.index(max(elements))


def argmin(elements: list):# -> int:
    # return the index of the highest value in the sequence
    return elements.index(min(elements))


SOLUTION = [
    1, 2, 3, 4, 5, 6, 7, 8, 9,
    7, 6, 9, 3, 2, 8, 1, 4, 5,
    4, 8, 5, 1, 9, 7, 6, 3, 2,
    9, 3, 4, 8, 6, 1, 2, 5, 7,
    8, 1, 7, 2, 3, 5, 9, 6, 4,
    6, 5, 2, 9, 7, 4, 8, 1, 3,
    3, 9, 1, 6, 4, 2, 5, 7, 8,
    2, 7, 6, 5, 8, 3, 4, 9, 1,
    5, 4, 8, 7, 1, 9, 3, 2, 6]
