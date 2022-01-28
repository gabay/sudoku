import os
import sys
import time

import sudoku


def timeit(f, title=None):
    start = time.time()
    result = f()
    end = time.time()
    if title:
        print(title)
    print("Time taken: %.02f" % (end - start))
    return result


def test_solving_time():
    def f1():
        s = sudoku.Sudoku()
        return sudoku.solve(s)

    timeit(f1, "Backtracking")

    def f2():
        s = sudoku.Sudoku()
        for i in range(9):
            s[i] = i + 1
        return sudoku.solve_sat(s)

    print(timeit(f2, "SAT solving (with 9 assignments)"))


def recognize_image(path):
    s = sudoku.Sudoku.fromimage(path)
    print(s)


def main(path):
    # test_solving_time()

    recognize_image(path)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print(f"Usage: {os.path.basename(sys.argv[0])} SUDOKU_IMAGE")
    else:
        main(sys.argv[1])
