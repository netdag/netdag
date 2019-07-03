TEST_GAMMA = 1
TEST_D_N = 2


def TEST_LAMBDA(n):
    from scipy.special import expit
    if n < TEST_D_N:
        return 0.0
    else:
        return float(expit(n/2))

def LOG(f):
    from numpy import log
    return float(log(f))
