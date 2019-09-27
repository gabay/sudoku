import os
import sys
import matplotlib.pyplot as plt
import numpy as np
import cv2 as cv
import pytesseract


def plot(image, name=None):
    plt.imshow(image, cmap='gray')
    if name:
        plt.title(name)
    plt.show()


def argmax(elements: list) -> int:
    # return the index of the highest value in the sequence
    return elements.index(max(elements))


def argmin(elements: list) -> int:
    # return the index of the highest value in the sequence
    return elements.index(min(elements))


def extract_digit(image):
    #plot(image)

    # threshold
    threshold = cv.adaptiveThreshold(image, 255, cv.ADAPTIVE_THRESH_GAUSSIAN_C, cv.THRESH_BINARY_INV, 11, 2)

    # loop through th middle of the image, looking for greatest area
    y, x = threshold.shape
    max_area = 0
    seed = (-1, -1)

    # Look for digit in the center of the image
    for yi in range(y // 3, y * 2 // 3):
        for xi in range(x // 3, x * 2 // 3):
            if threshold.item(yi, xi) == 255:
                area = cv.floodFill(threshold, None, (xi, yi), 255)
                if max_area < area[0]:
                    max_area = area[0]
                    seed = (xi, yi)
    print(max_area)
    # if the artifact is less than 5% of the image - assume there is not digit
    if max_area < (x * y) / 20:
        return 0

    # TODO: else - extract the digit
    return 1


def biggest_bounding_box(threshold):
    contours, hierarchy = cv.findContours(threshold, cv.RETR_TREE, cv.CHAIN_APPROX_SIMPLE)
    return contours[argmax(list(map(cv.contourArea, contours)))]


def contour_to_rect(contour):
    x = list(map(lambda point: point[0][0], contour))
    y = list(map(lambda point: point[0][1], contour))
    x_plus_y = list(map(lambda a, b: a + b, x, y))
    x_minus_y = list(map(lambda a, b: a - b, x, y))
    topleft = contour[argmin(x_plus_y)]
    topright = contour[argmax(x_minus_y)]
    bottomleft = contour[argmin(x_minus_y)]
    bottomright = contour[argmax(x_plus_y)]
    return np.float32([topleft, topright, bottomright, bottomleft])


def crop(image, src_rect, dst_width, dst_height):
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


def extract_sudoku(path):
    # read image as grayscale
    image = cv.imread(path, cv.IMREAD_GRAYSCALE)
    threshold = cv.adaptiveThreshold(image, 255, cv.ADAPTIVE_THRESH_GAUSSIAN_C, cv.THRESH_BINARY_INV, 11, 10)
    # plot(threshold)
    contour = biggest_bounding_box(threshold)
    # cv.drawContours(image, [contour], 0, 255, 3)
    transformed = crop(image, contour_to_rect(contour), 28 * 9, 28 * 9)
    plot(transformed)
    return list(map(extract_digit, subimages(transformed, 9, 9)))


def save_as_txt(sudoku, path):
    assert len(sudoku) == 81
    with open(path, 'w') as out:
        for index, number in enumerate(sudoku):
            out.write(str(number) if number != 0 else '_')
            if index % 9 == 8:
                out.write('\n')
            elif index % 3 == 2:
                out.write(' ')


def main(args):
    path = 'sudoku.jpg' if len(args) == 0 else args[0]
    result = extract_sudoku(path)
    print(result)
    save_as_txt(result, 'sudoku_from_image.txt')


if __name__ == '__main__':
    main(sys.argv[1:])
