
def main():
    chance = 1.5
    assert chance >= 0, 'Ontological Error: chance violated nature of Probability at boundary chance >= 0'
    assert chance <= 1, 'Ontological Error: chance violated nature of Probability at boundary chance <= 1'
    print(chance)

if __name__ == "__main__":
    main()