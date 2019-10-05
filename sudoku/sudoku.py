import sys
import re
from . import mycv


def row(index):
    yield from range(index - (index % 9), index - (index % 9) + 9)


def col(index):
    yield from range(index % 9, 81, 9)


def box(index):
    col = index % 9
    row = index - col
    box_x = col - (col % 3)
    box_y = row - (row % 27)
    box_start = box_y + box_x
    yield from range(box_start, box_start + 3)
    yield from range(box_start + 9, box_start + 12)
    yield from range(box_start + 18, box_start + 21)


class Sudoku:
    def __init__(self, cells=None):
        if cells is None:
            cells = [0 for _ in range(81)]
        assert len(cells) == 81
        assert all(isinstance(i, int) for i in cells)
        self.cells = list(cells)

    @classmethod
    def fromtxt(cls, path):
        with open(path) as inp:
            # allow digits and underscores
            data = inp.read().replace('_', '0')
            cells = list(map(int, re.findall(r'\d', data)))
            return Sudoku(cells)

    @classmethod
    def fromimage(cls, path):
        return Sudoku(mycv.extract_sudoku(path))

    def __str__(self):
        return '\n'.join(' '.join(map(str, self.cells[9 * i:9 * (i + 1)])) for i in range(9))

    def __getitem__(self, index):
        return self.cells[self._index(index)]

    def __setitem__(self, index, value):
        self.cells[self._index(index)] = value

    def __eq__(self, other):
        return self.cells == other.cells

    def _index(self, index):
        if isinstance(index, int):
            return index
        else:
            return (index[0] * 9) + index[1]

    def is_full(self):
        return 0 not in self.cells


def serialize(sudoku):
    return ''.join(map(str, sudoku.cells))


def deserialize(digits):
    padded_cells = list(map(int, digits)) + [0 for _ in range(81)]
    return Sudoku(padded_cells[:81])
