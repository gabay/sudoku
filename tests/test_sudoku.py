import sudoku


def test_sudoku_construction():
    s1 = sudoku.Sudoku()
    cells = [0 for _ in range(81)]
    s2 = sudoku.Sudoku(cells)
    assert cells is not s2.cells
    assert s1 == s2


def test_sudoku_getter_setter():
    s = sudoku.Sudoku()
    assert s[10] == 0
    assert s[1, 1] == 0
    s[10] = 1
    assert s[10] == 1
    assert s[1, 1] == 1


def test_row():
    l1 = list(range(0, 9))
    for i in l1:
        assert list(sudoku.row(i)) == l1
    l2 = list(range(9, 18))
    for i in l2:
        assert list(sudoku.row(i)) == l2
    l3 = list(range(72, 81))
    for i in l3:
        assert list(sudoku.row(i)) == l3


def test_col():
    c1 = list(range(0, 81, 9))
    for i in c1:
        assert list(sudoku.col(i)) == c1
    c2 = list(range(1, 81, 9))
    for i in c2:
        assert list(sudoku.col(i)) == c2
    c3 = list(range(7, 81, 9))
    for i in c3:
        assert list(sudoku.col(i)) == c3


def test_box():
    b1 = [0, 1, 2, 9, 10, 11, 18, 19, 20]
    for i in b1:
        assert list(sudoku.box(i)) == b1
    b2 = [33, 34, 35, 42, 43, 44, 51, 52, 53]
    for i in b2:
        assert list(sudoku.box(i)) == b2
    b3 = [57, 58, 59, 66, 67, 68, 75, 76, 77]
    for i in b3:
        assert list(sudoku.box(i)) == b3
