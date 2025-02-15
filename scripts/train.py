def train(x, y):
    return x + y

def test_train():
    assert train(1, 2) == 3
    assert train(2, 3) == 5
    assert train(3, 4) == 7