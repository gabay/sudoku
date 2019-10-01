import copy
from typing import Optional

from .sudoku import Sudoku, row, col, box
from .util import argmin


def trim_options(options, index, value):# -> None:
    # remove value from row
    [options[i].remove(value) for i in row(index) if value in options[i]]
    # remove value from col
    [options[i].remove(value) for i in col(index) if value in options[i]]
    # remove value from box
    [options[i].remove(value) for i in box(index) if value in options[i]]
    # add value to current cell
    options[index] = {value}


def get_options(sudoku):# -> list:
    options = [set(range(1, 10)) for _ in range(81)]
    for index, value in enumerate(sudoku.cells):
        if value != 0:
            trim_options(options, index, value)
    return options


def is_solvable(options):# -> bool:
    return all([len(option) > 0 for option in options])


def solve(s: Sudoku):# -> Optional[Sudoku]:
    if s.is_full():
        return s

    options = get_options(s)
    if _solve(s, options):
        return s
    else:
        return None


def _solve(s: Sudoku, options: list):# -> bool:
    if s.is_full():
        return True
    if not is_solvable(options):
        return False

    # choose the cell with the least options
    cells = list(filter(lambda i: s[i] == 0, range(81)))
    scores = list(map(lambda i: len(options[i]), cells))
    cell = cells[argmin(scores)]

    # solve cell
    for new_value in options[cell]:
        s[cell] = new_value
        new_options = copy.deepcopy(options)
        trim_options(new_options, cell, new_value)
        if _solve(s, new_options):
            return True

    # failed - reset cell
    s[cell] = 0
    return False
