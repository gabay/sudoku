import sys
import sudoku


def main(args):
    # solve an empty table
    s = sudoku.solve(sudoku.Sudoku())

    print('Solved empty sudoku:')
    print(s)

    # check if sat accepts it as a solution
    print('sat?')
    print(sudoku.sat.solve(s))


if __name__ == '__main__':
    main(sys.argv[1:])
