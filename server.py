import os
import sys
import tempfile

from flask import Flask, redirect, render_template, request

import sudoku

app = Flask("SudokuSolver")


@app.route("/", methods=["GET"])
def index_get():
    table = sudoku.deserialize(request.args.get("table", ""))
    message = request.args.get("message", "")
    return render_template("index.html", table=table, message=message)


@app.route("/", methods=["POST"])
def index_post():
    if "load" in request.form:
        s = image_to_sudoku(request.files.get("image"))
        if s:
            return redirect(f"/?table={sudoku.serialize(s)}&message=Loaded!")
        else:
            return redirect(f"/?message=Image loading failed :(")
    elif "backtrack" in request.form or "sat" in request.form:
        cells = [int(request.form["cell%d" % i] or 0) for i in range(81)]
        solver = sudoku.solve if "backtrack" in request.form else sudoku.solve_sat
        s = solver(sudoku.Sudoku(cells))
        if s:
            return redirect(f"/?table={sudoku.serialize(s)}&message=Solved!")
        else:
            return redirect("/?message=Solving failed :(")
    elif "clear" in request.form:
        return redirect("/?message=Cleared!")


def image_to_sudoku(image):  # -> Optional[sudoku.Sudoku]:
    if image:
        temp_path = tempfile.mktemp("_sudoku.jpg")
        image.save(temp_path)
        s = sudoku.Sudoku.fromimage(temp_path)
        os.unlink(temp_path)
        return s
    else:
        return None


def main(args):
    ssl_context = tuple(args) if len(args) == 2 else None
    host = "0.0.0.0"
    port = 80 if ssl_context is None else 443
    app.run(host, port, ssl_context=ssl_context)


if __name__ == "__main__":
    main(sys.argv[1:])
