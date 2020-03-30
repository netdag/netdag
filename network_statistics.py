__copyright__ = """
    Copyright 2020 Boston University Board of Trustees

    Author: Kacper Wardega
"""

__license__ = """
    This file is part of netdag.

    netdag is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    netdag is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with netdag.  If not, see <https://www.gnu.org/licenses/>.
"""

TEST_GAMMA = 1


def TEST_LAMBDA_SOFT(n):
    from scipy.special import expit
    if n < 1:
        return 0.0
    else:
        return float(expit(n))

def get_lambda_soft_from_mean_signal_strength(fSS):
    from numpy import e
    def lambda_soft(n):
        return 2 / (1 + e ** (-fSS * n)) - 1
    return lambda_soft

def TEST_LAMBDA_WEAKLY_HARD(n):
    return (max(0, 5-n), n*1000)


def LOG(f):
    from numpy import log
    return float(log(f))


def MIMO_lambda_weakly_hard(n):
    from math import floor, e
    return (int(floor(10 * e ** (-0.5 * n) + 1)), max(20, n*20))


def WH_cmp(x, y):
    from math import floor, ceil
    return y[0] <= max(floor(y[1]/x[1])*x[0], y[1]+ceil(y[1]/x[1])*(x[0]-x[1]))
