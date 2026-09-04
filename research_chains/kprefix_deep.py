"""Direct policy-gradient approximation to the epsilon_K ranking-menu objective."""
from __future__ import annotations

from dataclasses import dataclass
import time
from typing import Sequence

import numpy as np
import torch

from models.kprefix_net import KPrefixNet
from .kprefix import menu_metrics, optima_by_budget, prefix_mask


@dataclass(frozen=True)
class KPrefixInstance:
    features: np.ndarray
    values: np.ndarray
    m: int


def _sample_menu_regret(values: np.ndarray, m: int, menu: np.ndarray) -> tuple[float, float]:
    opt = optima_by_budget(values, m)
    regrets = []
    for k in range(1, m):
        achieved = min(float(values[prefix_mask(r, k)]) for r in menu)
        regrets.append(achieved - opt[k])
    return float(max(regrets, default=0.0)), float(np.mean(regrets) if regrets else 0.0)


def train_kprefix_net(
    instances: Sequence[KPrefixInstance],
    *,
    K: int,
    epochs: int = 300,
    lr: float = 3e-3,
    hidden_dim: int = 128,
    entropy_weight: float = 1e-3,
    mean_regret_weight: float = 0.1,
    seed: int = 0,
    device: str = "cpu",
) -> tuple[KPrefixNet, dict]:
    if not instances:
        raise ValueError("training requires at least one instance")
    m = int(instances[0].m)
    input_dim = int(np.asarray(instances[0].features).size)
    if any(int(x.m) != m or np.asarray(x.features).size != input_dim for x in instances):
        raise ValueError("training instances must have fixed m and feature dimension")
    torch.manual_seed(int(seed)); np.random.seed(int(seed))
    model = KPrefixNet(input_dim, m, int(K), hidden_dim=hidden_dim).to(device)
    opt = torch.optim.Adam(model.parameters(), lr=float(lr))
    baseline = None
    history = []
    started = time.perf_counter()
    for epoch in range(int(epochs)):
        order = np.random.permutation(len(instances))
        losses = []; regrets = []
        for idx in order:
            inst = instances[int(idx)]
            feat = torch.tensor(inst.features, dtype=torch.float32, device=device).unsqueeze(0)
            menu, logp, entropy = model.sample_rankings(feat)
            menu_np = menu[0].detach().cpu().numpy()
            worst, mean = _sample_menu_regret(inst.values, m, menu_np)
            objective = worst + float(mean_regret_weight) * mean
            baseline = objective if baseline is None else 0.95 * baseline + 0.05 * objective
            advantage = float(objective - baseline)
            loss = advantage * logp.mean() - float(entropy_weight) * entropy.mean()
            opt.zero_grad(); loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 5.0)
            opt.step()
            losses.append(float(loss.item())); regrets.append(float(worst))
        if epoch % max(1, int(epochs) // 20) == 0 or epoch == int(epochs) - 1:
            history.append({
                "epoch": int(epoch),
                "mean_reinforce_loss": float(np.mean(losses)),
                "mean_sampled_worst_regret": float(np.mean(regrets)),
                "baseline": None if baseline is None else float(baseline),
            })
    return model, {
        "epochs": int(epochs),
        "train_seconds": float(time.perf_counter() - started),
        "history": history,
        "parameter_bytes": model.parameter_bytes(),
        "seed": int(seed),
    }


def evaluate_kprefix_net(model: KPrefixNet, instances: Sequence[KPrefixInstance], device: str = "cpu") -> dict:
    rows = []
    times = []
    for inst in instances:
        feat = torch.tensor(inst.features, dtype=torch.float32, device=device).unsqueeze(0)
        start = time.perf_counter()
        ranking = model.greedy_rankings(feat)[0].cpu().numpy()
        times.append(time.perf_counter() - start)
        metrics = menu_metrics(inst.values, inst.m, ranking)
        rows.append(metrics)
    return {
        "instances": len(rows),
        "worst_budget_regret_mean": float(np.mean([r["worst_budget_regret"] for r in rows])) if rows else None,
        "mean_budget_regret_mean": float(np.mean([r["mean_budget_regret"] for r in rows])) if rows else None,
        "inference_seconds_mean": float(np.mean(times)) if times else None,
        "memory_bytes": int(model.parameter_bytes()),
        "policy_return": None,
        "policy_return_status": "NOT_AVAILABLE_IN_TIER_A_FINITE_WORLD",
        "rows": rows,
    }
