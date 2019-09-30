import sys
from flask import Flask, request, render_template
import sudoku
app = Flask('SudokuSolver')


@app.route('/', methods=['GET', 'POST'])
def index():
    table = None
    if request.method == 'POST':
        if 'image' in request.form and request.form['image'] != '':
            print('LOAD REQUEST')
            image = request.form['image']
            s = sudoku.Sudoku.fromimage(image)
            print(s)
            table = s.cells
        elif 'cell0' in request.form:
            print('SOLVE REQUEST')
            cells = [int(request.form[f'cell{i}'] or 0) for i in range(81)]
            s = sudoku.solve(sudoku.Sudoku(cells))
            table = s.cells
    return render_template('index.html', table=table)


def main(args):
    app.run('', 80)


if __name__ == '__main__':
    main(sys.argv[1:])
