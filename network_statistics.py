TEST_GAMMA = 1
TEST_D_N = 2


def TEST_LAMBDA(n):
    from scipy.stats import expit
    if n < TEST_D_N:
        return 0.0
    else:
        return expit(n)
