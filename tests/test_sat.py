import sudoku


def test_sat_solve_returns_none():
    s = sudoku.Sudoku()
    s[0] = 1
    s[1] = 1
    assert sudoku.solve_sat(s) is None


def test_sat_solve_on_complete_board():
    s = sudoku.Sudoku(sudoku.util.SOLUTION)
    assert sudoku.solve_sat(s) is not None
    s[0] = 0
    assert sudoku.solve_sat(s) is not None
