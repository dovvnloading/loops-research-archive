from fractions import Fraction


class QRoot:
    """a + b*sqrt(-3), with exact rational coefficients."""

    def __init__(self, a=0, b=0):
        self.a = Fraction(a)
        self.b = Fraction(b)

    def __add__(self, other):
        return QRoot(self.a + other.a, self.b + other.b)

    def __sub__(self, other):
        return QRoot(self.a - other.a, self.b - other.b)

    def __mul__(self, other):
        return QRoot(self.a * other.a - 3 * self.b * other.b,
                     self.a * other.b + self.b * other.a)

    def __neg__(self):
        return QRoot(-self.a, -self.b)

    def __pow__(self, n):
        out = QRoot(1)
        for _ in range(n):
            out = out * self
        return out

    def __eq__(self, other):
        return self.a == other.a and self.b == other.b

    def __repr__(self):
        return f"({self.a})+({self.b})sqrt(-3)"


def poly_add(left, right):
    out = [QRoot() for _ in range(max(len(left), len(right)))]
    for i, value in enumerate(left):
        out[i] = out[i] + value
    for i, value in enumerate(right):
        out[i] = out[i] + value
    while len(out) > 1 and out[-1] == QRoot():
        out.pop()
    return out


def poly_scale(poly, scalar):
    return [scalar * value for value in poly]


def poly_mul(left, right):
    out = [QRoot() for _ in range(len(left) + len(right) - 1)]
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i + j] = out[i + j] + a * b
    while len(out) > 1 and out[-1] == QRoot():
        out.pop()
    return out


def iterate_g_three_times():
    # In local coordinates w=z-z_alpha, f_c(z_alpha+w)-z_alpha=lambda*w+w^2.
    lam = QRoot(Fraction(-1, 2), Fraction(1, 2))
    current = [QRoot(), QRoot(1)]
    g = [QRoot(), lam, QRoot(1)]
    for _ in range(3):
        current = poly_add(poly_scale(current, lam), poly_mul(current, current))
    return lam, current


def main():
    lam = QRoot(Fraction(-1, 2), Fraction(1, 2))
    z_alpha = lam * QRoot(Fraction(1, 2))
    c = z_alpha - z_alpha ** 2
    lam3 = lam ** 3
    lam_sum = QRoot(1) + lam + lam ** 2
    _, germ = iterate_g_three_times()
    checks = {
        "primitive_third_root": lam ** 3 == QRoot(1),
        "nontrivial_rotation": lam != QRoot(1),
        "fixed_point_parameterization": z_alpha ** 2 + c == z_alpha,
        "period_three_multiplier_one": lam3 == QRoot(1),
        "root_of_unity_cancellation": lam_sum == QRoot(),
        "parabolic_germ_has_no_quadratic_term": len(germ) > 2 and germ[2] == QRoot(),
        "parabolic_germ_has_no_cubic_term": len(germ) > 3 and germ[3] == QRoot(),
        "quartic_term_nonzero": len(germ) > 4 and germ[4] != QRoot(),
    }
    result = {
        "certificate": "PARABOLIC_SATELLITE_ANCHOR_VALID",
        "lambda": repr(lam),
        "z_alpha": repr(z_alpha),
        "c_1_over_3": repr(c),
        "f3_local_germ_coefficients": [repr(value) for value in germ[:5]],
        "checks": checks,
        "all_checks": all(checks.values()),
        "original_artifacts_written": False,
    }
    print(result)
    if not result["all_checks"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
