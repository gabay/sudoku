import sys
from flask import Flask, request, render_template
import sudoku
app = Flask('SudokuSolver')

PAGE = '''
<html>
    <head>
        <title>Sudoku Solver</title>
    </head>
    <body>
        <h1>Sudoku solver</h1>
        <form method="post">
            Image:<input type="file" name="image"/><br/>
            <input type="submit" value="Solve"/>
        </form>
        <table>
            <tr><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td></tr>
            <tr><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td></tr>
            <tr><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td></tr>
            <tr><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td></tr>
            <tr><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td></tr>
            <tr><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td></tr>
            <tr><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td></tr>
            <tr><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td></tr>
            <tr><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td></tr>
        </table>
    </body>
</html>'''


@app.route('/', methods=['GET', 'POST'])
def index():
    solved = [''] * 81
    if request.method == 'POST':
        image = request.form['image']
        s = sudoku.Sudoku.fromimage(image)
        print(s)
        solved = sudoku.solve(s)
        print(solved)
        solved = solved.cells
    return PAGE.format(*solved)


def main(args):
    app.run('', 80)


if __name__ == '__main__':
    main(sys.argv[1:])
