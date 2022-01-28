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


def recognize_image():
    image = "s.jpg"
    s = sudoku.Sudoku.fromimage(image)
    print(s)


def main(args):
    # test_solving_time()

    recognize_image()


if __name__ == "__main__":
    main(sys.argv[1:])
