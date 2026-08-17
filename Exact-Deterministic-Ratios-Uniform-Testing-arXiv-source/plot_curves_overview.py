"""Generate the two competitive-ratio curves used in the introduction."""

import matplotlib.pyplot as plt
import numpy as np
from scipy.optimize import brentq


PHI = (1 + np.sqrt(5)) / 2
U_DIAMOND = (1 + np.sqrt(3 + 2 * np.sqrt(5))) / 2
S_ZERO = brentq(lambda s: s**3 - (s + 1) ** 2, 1, 3)
U_ZERO = 1 + S_ZERO
Z_STAR = brentq(lambda z: z - 3 - np.log(z), 4, 5)
R_STAR = 1 + 2 / (Z_STAR - 1)

U_R = 5.048917339522306
U_PLATEAU = 25 / 4
U_RAND_MAX = (3 + np.sqrt(3)) / 2
R_RAND_MAX = (27 + 6 * np.sqrt(3)) / 23


def rho_i(u):
    s = u - 1
    b = s**3 + s**2 + 1
    c = -(s**2 + s + 1) * (s + 2)
    return (-b + np.sqrt(b**2 - 4 * s * c)) / (2 * s)


def c_mix(u):
    lo = 2 / (Z_STAR - 1)
    hi = 1 / PHI

    def equation(c):
        m = 1 + 2 / c - u
        return np.arctanh(m) - m - (1 - 1 / c + 0.5 * np.log(1 + 2 / c))

    if abs(equation(lo)) < 1e-10:
        return 1 + lo
    if abs(equation(hi)) < 1e-10:
        return 1 + hi
    return 1 + brentq(equation, lo, hi)


def rand_middle_one(u):
    return u**3 / (u**2 + (u - 1) ** 3)


def rand_middle_two(u):
    return 1 + 1 / (2 * (np.sqrt(u) - 1))


fig, (left, right) = plt.subplots(1, 2, figsize=(7.4, 3.0))

segments = [
    (np.linspace(0.2, 1, 80), lambda u: np.ones_like(u)),
    (np.linspace(1, U_DIAMOND, 100), lambda u: u),
    (np.linspace(U_DIAMOND, U_ZERO, 140), rho_i),
    (np.linspace(U_ZERO, PHI + 2, 100), lambda u: 1 + 1 / np.sqrt(u - 1)),
    (np.linspace(PHI + 2, Z_STAR, 100), lambda u: np.array([c_mix(x) for x in u])),
    (np.linspace(Z_STAR, 7.3, 100), lambda u: np.full_like(u, R_STAR)),
]
for x, fn in segments:
    left.plot(x, fn(x), color="#2878b5", linewidth=2.5)
for transition in (1, U_DIAMOND, U_ZERO, PHI + 2, Z_STAR):
    left.axvline(transition, color="0.62", linestyle=(0, (2, 3)), linewidth=0.7)
left.scatter([U_DIAMOND, Z_STAR], [U_DIAMOND, R_STAR], color="black", s=20, zorder=5)
left.annotate(
    r"maximum $1.86676\ldots$",
    xy=(U_DIAMOND, U_DIAMOND), xytext=(2.45, 1.84),
    arrowprops={"arrowstyle": "-", "color": "0.35", "linewidth": 0.7},
    fontsize=8,
)
left.annotate(r"$1.57057\ldots$", xy=(6.25, R_STAR), xytext=(5.3, 1.61), fontsize=8)
left.set_title("deterministic")
left.set_ylabel("optimal competitive ratio")

x = np.linspace(0.2, 1, 80)
right.plot(x, np.ones_like(x), color="#e87511", linewidth=2.5)
x = np.linspace(1, U_R, 350)
right.plot(x, rand_middle_one(x), color="#e87511", linewidth=2.5)
x = np.linspace(U_R, U_PLATEAU, 120)
right.plot(x, rand_middle_two(x), color="#e87511", linewidth=2.5)
x = np.linspace(U_PLATEAU, 7.3, 80)
right.plot(x, np.full_like(x, 4 / 3), color="#e87511", linewidth=2.5)
for transition in (1, U_R, U_PLATEAU):
    right.axvline(transition, color="0.62", linestyle=(0, (2, 3)), linewidth=0.7)
right.scatter(
    [U_RAND_MAX, U_R, U_PLATEAU],
    [R_RAND_MAX, rand_middle_one(U_R), 4 / 3],
    color="black", s=20, zorder=5,
)
right.annotate(
    r"maximum $1.62575\ldots$",
    xy=(U_RAND_MAX, R_RAND_MAX), xytext=(3.05, 1.64),
    arrowprops={"arrowstyle": "-", "color": "0.35", "linewidth": 0.7},
    fontsize=8,
)
right.annotate(r"$4/3$", xy=(6.7, 4 / 3), xytext=(6.55, 1.37), fontsize=9)
right.set_title("randomized")

for ax in (left, right):
    ax.set_xlim(0.2, 7.3)
    ax.set_ylim(0.97, 1.91)
    ax.set_xlabel(r"raw execution time $u$")
    ax.grid(axis="y", color="0.84", linewidth=0.6)
    ax.spines[["top", "right"]].set_visible(False)
    ax.tick_params(labelsize=8)

fig.tight_layout(w_pad=2.0)
fig.savefig("curves_overview.pdf", bbox_inches="tight")
