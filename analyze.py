by_poly = {}

num_knots = 0

with open("2022-04-17-knots-unoriented.txt") as fin:
    for name in fin:
        num_knots += 1

        poly1 = next(fin)
        poly2 = next(fin)

        key = poly1 + poly2
        by_poly.setdefault(key, []).append(name)

print(f"Loaded {num_knots} knots; {len(by_poly)} different polynomials")

for key, knots in by_poly.items():
    if len(knots) > 1 :
        print("nonunique class: " + repr(knots))
