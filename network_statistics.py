TEST_GAMMA = 1


def TEST_LAMBDA_SOFT(n):
    from scipy.special import expit
    if n < 1:
        return 0.0
    else:
        return float(expit(n))


def TEST_LAMBDA_WEAKLY_HARD(n):
    return (max(0, 5-n), 1000)


def LOG(f):
    from numpy import log
    return float(log(f))
