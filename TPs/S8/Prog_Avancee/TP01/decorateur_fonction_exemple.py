def fn_bavard(f):

    def f_interne(*p, **k):
        print('debut de f_interne()')
        f(*p, **k)
        print('fin de f_interne()')

    print('dans fn_bavard')
    return f_interne


def deprecated(f):

    def f_interne(*p, **kw):
        print("Deprecated")
        f(*p, **kw)

    return f_interne


@fn_bavard
@deprecated
def exemple(x, y='ok'):
    print('exemple:', y, x)


print('Appel à exemple')
exemple('?')
print(exemple.__qualname__)
