import sys
import re
import copy
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
        else:
            cells = list(cells)
        assert len(cells) == 81
        assert all(isinstance(i, int) for i in cells)
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

    def empty(self, index):
        return self[index] == 0

    def is_full(self):
        return 0 not in self.cells


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


def solve(s, options=None) -> Sudoku:
    if s.is_full():
        return s

    if options is None:
        options = get_options(s)

    # choose the cell with the least options
    cell, score = -1, -1
    for index, value in enumerate(s):
        if value == 0 and get_score(options[index]) > score:
            cell, score = index, get_score(options[index])
    if cell != -1:
        # solve it
        for new_value in options[cell]:
            s[cell] = new_value
            new_options = copy.deepcopy(options)
            trim_options(new_options, cell, new_value)
            # continue only if soduko is still solvable
            if is_solvable(new_options):
                if solve(s, new_options).is_full():
                    break
        else:
            # failed - reset cell
            s[cell] = 0
    return s


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
