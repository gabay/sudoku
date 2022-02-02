import os
import sys

import cv2 as cv
import numpy as np

from . import mycv


def get_digit(digit_image):  # -> int:
    return DigitRecognizer.get_digit(digit_image)


class DigitRecognizer:
    TRAIN_FILE = "digits.png"
    MODEL_FILE = "digit_recognizer.dat"
    MODEL = None
    SIZE = (20, 15)

    def __init__(self):
        raise NotImplementedError("This class is used as a namespace")

    @classmethod
    def get_digit(cls, image):  # -> int:
        features = np.array([cls.resize(image)])
        retval, result = cls.get_model().predict(features)
        # print(int(result[0][0]))
        # mycv.plot(image)
        return int(result[0][0])

    @classmethod
    def resize(cls, image):
        return np.array(np.reshape(cv.resize(image, cls.SIZE), -1), dtype=np.float32)

    @classmethod
    def get_model(cls):
        if cls.MODEL is None:
            # load model
            if os.path.isfile(cls.MODEL_FILE):
                cls.MODEL = cv.ml.SVM_load(cls.MODEL_FILE)
            else:
                # train and save model
                r = cv.ml.SVM_create()
                r.setKernel(cv.ml.SVM_LINEAR)
                r.setType(cv.ml.SVM_C_SVC)
                train, labels = cls.load_train_data()
                r.train(train, cv.ml.ROW_SAMPLE, labels)
                # save model
                r.save(cls.MODEL_FILE)
                cls.MODEL = r
        return cls.MODEL

    @classmethod
    def load_train_data(cls):
        image = cv.imread(cls.TRAIN_FILE, cv.IMREAD_GRAYSCALE)
        _, threshold = cv.threshold(image, 240, 255, cv.THRESH_BINARY_INV)
        contours, hierarchy = cv.findContours(threshold, cv.RETR_EXTERNAL, cv.CHAIN_APPROX_SIMPLE)
        bounding_boxes = list(map(mycv.bounding_box, contours))
        # sort by x position and label 0-9
        bounding_boxes.sort(key=lambda box: box[0][0])

        # cv.drawContours(image, np.array(bounding_boxes), -1, 128)
        # mycv.plot(image)

        # resize train data (and omit 0)
        train = np.array(
            [cls.resize(threshold[b[0][1] : b[1][1], b[0][0] : b[1][0]]) for b in bounding_boxes]
        )[1:]
        labels = np.arange(1, 10)

        return train, labels


def main(args):
    data = DigitRecognizer.load_train_data()
    print(data)
    print([i.shape for i in data[0]])


if __name__ == "__main__":
    main(sys.argv[1:])
