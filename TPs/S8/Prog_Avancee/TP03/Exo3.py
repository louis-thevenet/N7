class Proxy:

    def __init__(self, obj, forbidden_methods):
        self.obj = obj
        self.forbidden_methods = forbidden_methods

    def invoke(self, method, *args):
        if method in self.forbidden_methods:
            raise AttributeError("Forbidden method")
        return getattr(self.obj, method)(*args)


def main():
    print("Exo 3")
    p = Proxy("hello", ["lower"])
    assert p.invoke("upper") == "HELLO"
    p.invoke("lower")


if __name__ == "__main__":
    main()
