from typing import Optional
import z3
import sudoku


def solve(s: sudoku.Sudoku) -> Optional[sudoku.Sudoku]:
    constraints = _get_constraints(s)
    solver = z3.Solver()
    solver.add(constraints)
    if solver.check() == z3.sat:
        model = solver.model()
        # assume cell variables are entered in order...
        cells = [model.eval(var) for var in model.decls()]
        return sudoku.Sudoku(cells)
    else:
        return None


def _get_constraints(s: sudoku.Sudoku = None):
    cells = [z3.Int(f'cell{i:02}') for i in range(81)]

    # bound cell values
    val1 = [cell >= 1 for cell in cells]
    val2 = [cell <= 9 for cell in cells]
    row, col, box = [], [], []

    for i in range(81):
        # deny equal cells per row
        for j in sudoku.row(i):
            if i < j:
                row.append(cells[j] != cells[i])
        # deny equal cells per column
        for j in sudoku.col(i):
            if i < j:
                col.append(cells[j] != cells[i])
        # deny equal cells per box
        for j in sudoku.box(i):
            if i < j:
                box.append(cells[j] != cells[i])

    specific_constraints = []
    if s is not None:
        for cell, value in zip(cells, s.cells):
            if 1 <= value <= 9:
                specific_constraints.append(cell == value)

    return val1 + val2 + row, col, box + specific_constraints
