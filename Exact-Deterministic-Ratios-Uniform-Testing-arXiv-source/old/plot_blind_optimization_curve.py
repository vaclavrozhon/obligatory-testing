"""Compare revealing and non-revealing optimization."""

import matplotlib.pyplot as plt
import numpy as np


U_REVEAL_SWITCH = 5.048917339522306
U_REVEAL_PLATEAU = 25 / 4
U_BLIND_SWITCH = 2.246979603717467


def revealing_ratio(u):
    out = np.ones_like(u)
    mask = u > 1
    out[mask] = u[mask] ** 3 / (u[mask] ** 2 + (u[mask] - 1) ** 3)
    mask = u > U_REVEAL_SWITCH
    out[mask] = 1 + 1 / (2 * (np.sqrt(u[mask]) - 1))
    out[u >= U_REVEAL_PLATEAU] = 4 / 3
    return out


def blind_ratio(u):
    out = np.ones_like(u)
    mask = u > 1
    out[mask] = u[mask] ** 3 / (u[mask] ** 2 + (u[mask] - 1) ** 3)
    mask = u > U_BLIND_SWITCH
    out[mask] = 0.5 * (
        1 + np.sqrt((u[mask] ** 2 + u[mask] - 1) / (u[mask] - 1))
    )
    return out


u = np.linspace(0.2, 20, 1000)
fig, ax = plt.subplots(figsize=(7.2, 3.8))
ax.plot(u, revealing_ratio(u), linewidth=2.6, color="#e87511",
        label=r"optimization reveals $p_i$")
ax.plot(u, blind_ratio(u), linewidth=2.6, color="#6a51a3",
        label=r"optimization keeps $p_i$ hidden")
ax.axvline(1, color="0.65", linestyle=(0, (2, 3)), linewidth=0.8)
ax.axhline(4 / 3, color="0.72", linestyle=(0, (4, 3)), linewidth=0.8)
ax.annotate(r"$4/3$", xy=(18.4, 4 / 3), xytext=(18.4, 1.42), fontsize=10)
ax.annotate(
    r"grows as $\sqrt{u}/2$",
    xy=(15, blind_ratio(np.array([15.0]))[0]),
    xytext=(11.2, 2.85),
    arrowprops={"arrowstyle": "-", "color": "0.35", "linewidth": 0.8},
    fontsize=10,
)
ax.set_xlim(0.2, 20)
ax.set_ylim(0.95, 3.1)
ax.set_xlabel(r"raw execution time $u$")
ax.set_ylabel("optimal randomized ratio")
ax.grid(axis="y", color="0.84", linewidth=0.7)
ax.spines[["top", "right"]].set_visible(False)
ax.legend(frameon=False, loc="upper left")
fig.tight_layout()
fig.savefig("blind_optimization_curve.pdf", bbox_inches="tight")
