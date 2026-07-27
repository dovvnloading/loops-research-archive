from decimal import Decimal, getcontext

getcontext().prec = 80

def sector_step(theta):
    eps = 1 if theta > 0 else -1
    a = int((Decimal(1) / abs(theta)).to_integral_value(rounding="ROUND_FLOOR"))
    candidates = []
    for b in (a, a + 1):
        nxt = -Decimal(1) / theta + Decimal(eps * b)
        if abs(nxt) < Decimal("0.5") and nxt != 0:
            candidates.append((b, 1 if nxt > 0 else -1, nxt))
    if len(candidates) != 1:
        raise AssertionError((theta, a, candidates))
    return eps, a, candidates[0]

def check(theta0, levels=10):
    theta = Decimal(str(theta0))
    p = [Decimal(0)]
    q = [Decimal(1)]
    theta_values = [theta]
    eps_values = []
    abar_values = []
    b_values = []
    for _ in range(levels):
        eps, abar, (b, next_eps, theta_next) = sector_step(theta)
        eps_values.append(eps)
        abar_values.append(abar)
        b_values.append(b)
        theta_values.append(theta_next)
        theta = theta_next
    eps = eps_values
    p.append(Decimal(eps[0]))
    q.append(Decimal(b_values[0]))
    for n in range(1, levels):
        sign_term = Decimal(eps[n - 1] * eps[n])
        p.append(Decimal(b_values[n]) * p[n] - sign_term * p[n - 1])
        q.append(Decimal(b_values[n]) * q[n] - sign_term * q[n - 1])

    max_error = Decimal(0)
    for n in range(levels + 1):
        lhs = q[n] * theta_values[0] - p[n]
        sign_product = 1
        for e in eps[:n]:
            sign_product *= e
        product = Decimal(sign_product)
        for t in theta_values[: n + 1]:
            product *= t
        error = abs(lhs - product)
        max_error = max(max_error, error)
        if error > Decimal("1e-60"):
            raise AssertionError((theta0, n, lhs, product, error))
    return {
        "theta0": str(theta0),
        "levels": levels,
        "max_abs_error": str(max_error),
        "first_return_time": str(q[1]),
        "first_digit": abar_values[0],
        "signs": eps,
        "digits": abar_values,
        "returns": [str(x) for x in q],
    }

if __name__ == "__main__":
    cases = ["0.3141592653589793", "-0.2718281828459045", "0.4142135623730951"]
    records = [check(x, 12) for x in cases]
    for record in records:
        print(record)
    large_digit = check("0.0001234567890123", 6)
    print(large_digit)
    if large_digit["first_digit"] < 8000:
        raise AssertionError(large_digit)
    print({"certificate": "SECTOR_ARITHMETIC_VALID", "all_checks": True})

