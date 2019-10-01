import sys
from typing import Optional

from flask import Flask, request, render_template
import sudoku
app = Flask('SudokuSolver')


@app.route('/', methods=['GET', 'POST'])
def index():
    table = None
    message = ''
    if request.method == 'POST':
        print(request.form)
        print(request.files)
        if 'load' in request.form:
            s = image_to_sudoku(request.files.get('image'))
            if s is None:
                message = 'Failed to load :('
            else:
                message = 'Loaded!'
                table = s.cells
        elif 'backtrack' in request.form or 'sat' in request.form:
            cells = [int(request.form[f'cell{i}'] or 0) for i in range(81)]
            solver = sudoku.solve if 'backtrack' in request.form else sudoku.solve_sat
            s = solver(sudoku.Sudoku(cells))
            if s is None:
                message = 'Failed to solve :('
                table = cells
            else:
                message = 'Solved!'
                table = s.cells
    return render_template('index.html', table=table, message=message)


def image_to_sudoku(image) -> Optional[sudoku.Sudoku]:
    if image:
        image.save('_sudoku.jpg')
        return sudoku.Sudoku.fromimage('_sudoku.jpg')
    else:
        return None


def main(args):
    app.run('', 80)


if __name__ == '__main__':
    main(sys.argv[1:])
