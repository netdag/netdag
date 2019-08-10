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
