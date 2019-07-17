TEST_GAMMA = 1


def TEST_LAMBDA(n):
    from scipy.special import expit
    if n < 1:
        return 0.0
    else:
        return float(expit(n))


def TEST_BETA(n):
    return (1, 1000)


def LOG(f):
    from numpy import log
    return float(log(f))
