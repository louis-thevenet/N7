import functools

global depth
depth = 4


def trace(f):

    @functools.wraps(f)
    def f_interne(*p, **k):
        global depth
        print(depth * ' ' + "--> " + f_interne.__qualname__ + str(p))
        depth += 2
        try:
            res = f(*p, **k)
            print(depth * ' ' + "<-- " + str(res))
            depth -= 2
            return res
        except Exception as e:
            print(depth * ' ' + "<-- " + e.__class__.__name__)
            depth -= 2
            raise e

    return f_interne


@trace
def fact(n):
    if n <= 1:
        return 1
    else:
        return n * fact(n - 1)


@trace
def est_pair(n):
    return n == 0 or est_impair(n - 1)


@trace
def est_impair(n):
    return n > 0 and est_pair(n - 1)


@trace
def fail_at_10(n):
    if n == 10:
        raise ArithmeticError
    else:
        return fail_at_10(n + 1)


def ihm():
    """Interface avec l'utilisateur."""
    x = 3
    print(f'fact({x}) =', fact(x))
    print(f'{x} est', 'pair' if est_pair(x) else 'impair')
    fail_at_10(0)


if __name__ == '__main__':
    ihm()
