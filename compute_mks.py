def P(u, scale=1, r=1.9):
    """Dynamic power: scale * (2u - u^r)."""
    return scale * (2 * u - u ** r)

width = 0.2
slopes = []
for k in range(1, 6):
    lo, hi = width * (k - 1), width * k
    m_k = (P(hi) - P(lo)) / width
    slopes.append(m_k)
    print(f"m_{k} = {m_k:.4f}   (segment {lo:.1f} to {hi:.1f})")

# Sanity check: the segments should add back up to P(1) = 1
print("sum of m_k * width =", round(sum(m * width for m in slopes), 4))