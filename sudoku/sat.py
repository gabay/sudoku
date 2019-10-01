from typing import Optional
import z3
from .sudoku import Sudoku, row, col, box


def solve(s: Sudoku) -> Optional[Sudoku]:
    cells, constraints = _get_constraints(s)
    solver = z3.Solver()
    solver.add(*constraints)
    if solver.check() == z3.sat:
        model = solver.model()
        return Sudoku([model[cell].as_long() for cell in cells])
    else:
        return None


def _get_constraints(s: Sudoku = None):
    cells = [z3.Int('cell%02d' % i) for i in range(81)]

    # bound cell values
    v1 = [cell >= 1 for cell in cells]
    v2 = [cell <= 9 for cell in cells]
    r, c, b = [], [], []

    for i in range(81):
        # deny equal cells per row
        for j in row(i):
            if i < j:
                r.append(cells[i] != cells[j])
        # deny equal cells per column
        for j in col(i):
            if i < j:
                c.append(cells[i] != cells[j])
        # deny equal cells per box
        for j in box(i):
            if i < j:
                b.append(cells[i] != cells[j])

    assignments = []
    if s is not None:
        for cell, value in zip(cells, s.cells):
            if 1 <= value <= 9:
                assignments.append(cell == value)

    constraints = v1 + v2 + r + c + b + assignments
    return cells, constraints


if __name__ == '__main__':
    s = solve(Sudoku())
    print('Solved empty sudoku:')
    print(s)
