import sys
import time
import sudoku


def timeit(f, title=None):
    start = time.time()
    result = f()
    end = time.time()
    if title:
        print(title)
    print(f'Time taken: {end - start:.2f}')
    return result


def main(args):
    def f1():
        s = sudoku.Sudoku()
        return sudoku.solve(s)

    timeit(f1, 'Backtracking')

    def f2():
        s = sudoku.Sudoku()
        s[0] = 1
        s[1] = 2
        s[2] = 3
        s[3] = 4
        s[4] = 5
        s[5] = 6
        s[6] = 7
        s[7] = 8
        s[8] = 9
        return sudoku.solve_sat(s)

    timeit(f2, 'SAT solving')


if __name__ == '__main__':
    main(sys.argv[1:])
