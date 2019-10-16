import sys

from flask import Flask, request, render_template, redirect
import sudoku

app = Flask('SudokuSolver')


@app.route('/', methods=['GET', 'POST'])
def index():
    if request.method == 'GET':
        table = sudoku.deserialize(request.args.get('table', ''))
        message = request.args.get('message', '')
        return render_template('index.html', table=table, message=message)
    elif request.method == 'POST':
        redirect_url = ''
        if 'load' in request.form:
            s = image_to_sudoku(request.files.get('image'))
            if s is None:
                redirect_url = '/?message=Failed to load :('
            else:
                redirect_url = f'/?table={sudoku.serialize(s)}&message=Loaded!'
        elif 'backtrack' in request.form or 'sat' in request.form:
            cells = [int(request.form['cell%d' % i] or 0) for i in range(81)]
            solver = sudoku.solve if 'backtrack' in request.form else sudoku.solve_sat
            s = solver(sudoku.Sudoku(cells))
            if s:
                redirect_url = '/?message=Failed to solve :('
            else:
                redirect_url = f'/?table={sudoku.serialize(s)}&message=Solved!'
        elif 'clear' in request.form:
            redirect_url = '/?message=Cleared!'
        return redirect(redirect_url)


def image_to_sudoku(image):  # -> Optional[sudoku.Sudoku]:
    if image:
        image.save('_sudoku.jpg')
        return sudoku.Sudoku.fromimage('_sudoku.jpg')
    else:
        return None


def main(args):
    ssl_context = tuple(args) if len(args) == 2 else None
    host = '0.0.0.0'
    port = 80 if ssl_context is None else 443
    app.run(host, port, ssl_context=ssl_context)


if __name__ == '__main__':
    main(sys.argv[1:])
