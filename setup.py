from setuptools import setup

setup(
    name="sudoku",
    version="1.0",
    description="Sudoku solver",
    url="https://github.com/gabay/sudoku",
    author="Roi Gabay",
    author_email="roigby@gmail.com",
    license="GPLv3",
    packages=["sudoku"],
    install_requires=["z3-solver", "opencv-python", "flask"],
)
