import sys

import cv2 as cv
import numpy as np

from . import digit_recognizer
from .util import argmax, argmin

# import matplotlib.pyplot as plt


# def plot(image):
#     plt.imshow(image, cmap='gray')
#     plt.show()

def plot(image):
    pass


def bounding_box(contour):
    x, y = list(map(lambda p: p[0][0], contour)), list(map(lambda p: p[0][1], contour))
    return [[min(x), min(y)], [max(x), max(y)]]


def biggest_bounding_box(threshold):
    contours, hierarchy = cv.findContours(threshold, cv.RETR_TREE, cv.CHAIN_APPROX_SIMPLE)
    return contours[argmax(list(map(cv.contourArea, contours)))]


def contour_to_rect(contour):# -> np.array:
    x = list(map(lambda point: point[0][0], contour))
    y = list(map(lambda point: point[0][1], contour))
    x_plus_y = list(map(lambda a, b: a + b, x, y))
    x_minus_y = list(map(lambda a, b: a - b, x, y))
    topleft = contour[argmin(x_plus_y)]
    topright = contour[argmax(x_minus_y)]
    bottomleft = contour[argmin(x_minus_y)]
    bottomright = contour[argmax(x_plus_y)]
    return np.float32([topleft, topright, bottomright, bottomleft])


def crop_and_warp(image, src_rect, dst_width, dst_height):
    dst_rect = np.float32([[0, 0], [dst_width, 0], [dst_width, dst_height], [0, dst_height]])
    # get contour
    m = cv.getPerspectiveTransform(src_rect, dst_rect)
    return cv.warpPerspective(image, m, (dst_width, dst_height))


def subimages(image, rows, cols):
    cell_x = image.shape[1] // 9
    cell_y = image.shape[0] // 9
    for y in range(rows):
        for x in range(cols):
            yield image[y * cell_y:(y + 1) * cell_y, x * cell_x:(x + 1) * cell_x]


def extract_digit(image):
    threshold = cv.adaptiveThreshold(image, 255, cv.ADAPTIVE_THRESH_GAUSSIAN_C, cv.THRESH_BINARY_INV, 11, 10)
    y, x = image.shape
    max_area = 0
    max_rect = None
    # Look for digit in the center of the image
    for yi in range(y // 3, y * 2 // 3):
        for xi in range(x // 3, x * 2 // 3):
            if threshold.item(yi, xi) == 255:
                area, _, _, rect = cv.floodFill(threshold, None, (xi, yi), 255)
                if max_area < area:
                    max_area = area
                    max_rect = rect
    # if the biggest is less than 4% of the image - assume it's empty
    if max_area < (x * y) / 25:
        return 0

    # else - extract the digit
    x, y, w, h = max_rect
    digit = digit_recognizer.get_digit(threshold[y:y + h, x:x + w])
    # print(digit)
    # plot(threshold[y:y + h, x:x + w])
    return digit


def extract_sudoku(path):# -> list:
    # read image as grayscale
    image = cv.imread(path, cv.IMREAD_GRAYSCALE)
    # plot(image)
    image = cv.resize(image, (800, 800))
    # plot(image)
    threshold = cv.adaptiveThreshold(image, 255, cv.ADAPTIVE_THRESH_GAUSSIAN_C, cv.THRESH_BINARY_INV, 11, 10)
    # plot(threshold)
    contour = biggest_bounding_box(threshold)
    # cv.drawContours(threshold, [contour], 0, 127, 7)
    # plot(threshold)
    transformed = crop_and_warp(image, contour_to_rect(contour), 28 * 9, 28 * 9)
    # plot(transformed)
    return list(map(extract_digit, subimages(transformed, 9, 9)))


def main(args):
    path = 'sudoku.jpg' if len(args) == 0 else args[0]
    result = extract_sudoku(path)
    print(result)


if __name__ == '__main__':
    main(sys.argv[1:])
