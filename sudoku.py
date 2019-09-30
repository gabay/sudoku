import os
import sys
import re
import copy
import mycv


def row(index):
    yield from range(index - (index % 9), index - (index % 9) + 9)


def col(index):
    yield from range(index % 9, 81, 9)


def box(index):
    box_x = (index // 3) % 3
    column = index % 9
    row = index - column
    box_start = index - (index % 27) + column
    yield from range(box_start, box_start + 3)
    yield from range(box_start + 9, box_start + 12)
    yield from range(box_start + 18, box_start + 21)


class Sudoku:
    def __init__(self, cells=None):
        if cells is None:
            cells = [0 for _ in range(81)]
        assert len(cells) == 81
        assert all(isinstance(i, int) for i in cells)
        self.size = 9
        self.cells = cells

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

    def copy(self):
        return Sudoku(self.cells)

    def row(self, index):
        start = self.size * index
        return self.cells[start:start + self.size]

    def col(self, index):
        return self.cells[index::self.size]

    def box(self, index):
        s = self.size
        r = (index // 3)
        c = (index % 3) * 3
        start = (r * s) + c
        return (self.cells[start:start + 3]
                + self.cells[start + s:start + s + 3]
                + self.cells[start + (2 * s):start + (2 * s) + 3])

    def __str__(self):
        s = self.size
        return '\n'.join(' '.join(map(str, self.cells[s * i:s * (i + 1)])) for i in range(self.size))

    def __getitem__(self, index):
        return self.cells[self._index(index)]

    def __setitem__(self, index, value):
        self.cells[self._index(index)] = value

    def _index(self, index):
        if isinstance(index, int):
            return index
        else:
            return (index[0] * self.size) + index[1]

    def empty(self, index):
        return self[index] == 0


def trim_options(options, index, value):
    # remove value from row
    [options[i].remove(value) for i in row(index) if value in options[i]]
    # remove value from col
    [options[i].remove(value) for i in col(index) if value in options[i]]
    # remove value from box
    [options[i].remove(value) for i in box(index) if value in options[i]]
    # add value to current cell
    options[index] = {value}


def get_options(sudoku):
    options = [set(range(1, 10)) for i in range(81)]
    for index, value in enumerate(sudoku.cells):
        if value != 0:
            trim_options(options, index, value)
    return options


def is_solvable(options):
    return all([len(option) > 0 for option in options])


def get_score(options):
    return 9 - len(options)


def solve(sudoku, options=None) -> Sudoku:
    if options is None:
        options = get_options(sudoku)

    # choose the cell with the least options
    cell, score = -1, -1
    for index, value in enumerate(sudoku):
        if value == 0 and get_score(options[index]) > score:
            cell, score = index, get_score(options[index])
    if cell != -1:
        # solve it
        for option in options[cell]:
            sudoku[cell] = option
            new_options = copy.deepcopy(options)
            trim_options(new_options, cell, option)
            # continue only if soduko is still solvable
            if is_solvable(new_options):
                solve(sudoku, new_options)
    return sudoku


def main(args):
    # from txt file
    s = Sudoku.fromtxt('sudoku.txt' if len(args) == 0 else args[0])
    print(' ========')
    print(' From TXT')
    print(' ========')
    print(s)
    print(get_options(s))
    print(solve(s))

    # from image
    print(' ========')
    print(' From JPG')
    print(' ========')
    s = Sudoku.fromimage('sudoku.jpg')
    print(s)
    print(get_options(s))
    print(solve(s))


if __name__ == '__main__':
    main(sys.argv[1:])
