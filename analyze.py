by_poly = {}
by_jpoly = {}

num_knots = 0

with open("2022-06-23-knots-unoriented.txt") as fin:
    for name in fin:
        num_knots += 1

        assert next(fin) == "arrow\n"
        poly1 = next(fin)
        poly2 = next(fin)
        key = poly1 + poly2
        by_poly.setdefault(key, []).append(name)

        assert next(fin) == "jones\n"
        jpoly1 = next(fin)
        jpoly2 = next(fin)
        key = jpoly1 + jpoly2
        by_jpoly.setdefault(key, []).append(name)

print(f"Loaded {num_knots} knots; {len(by_poly)} different arrow polynomials; {len(by_jpoly)} different jones polynomials")

print("arrow polynomial nonuniques")
for key, knots in by_poly.items():
    if len(knots) > 1 :
        print("nonunique class: " + repr(knots))

print("jones polynomial nonuniques")
for key, knots in by_jpoly.items():
    if len(knots) > 1 :
        print("nonunique class: " + repr(knots))
