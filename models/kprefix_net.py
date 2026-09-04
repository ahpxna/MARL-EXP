"""Neural ranking-menu policy for K-Prefix Incremental Optimisation."""
from __future__ import annotations

import torch
import torch.nn as nn


class KPrefixNet(nn.Module):
    """Map state/world features to K reusable full-ranking policies.

    A ranking head outputs Plackett-Luce logits over the m items.  Prefix
    consistency is therefore structural: every budget decision from one head
    is a prefix of the same sampled/greedy permutation.
    """

    def __init__(self, input_dim: int, m: int, K: int, hidden_dim: int = 128):
        super().__init__()
        self.input_dim = int(input_dim)
        self.m = int(m)
        self.K = int(K)
        self.encoder = nn.Sequential(
            nn.Linear(self.input_dim, hidden_dim),
            nn.ReLU(),
            nn.Linear(hidden_dim, hidden_dim),
            nn.ReLU(),
        )
        self.head = nn.Linear(hidden_dim, self.K * self.m)

    def forward(self, features: torch.Tensor) -> torch.Tensor:
        if features.ndim == 1:
            features = features.unsqueeze(0)
        z = self.encoder(features)
        return self.head(z).view(features.shape[0], self.K, self.m)

    @torch.no_grad()
    def greedy_rankings(self, features: torch.Tensor) -> torch.Tensor:
        logits = self.forward(features)
        return torch.argsort(logits, dim=-1, descending=True)

    def sample_rankings(self, features: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        """Sample K Plackett-Luce rankings and return permutation/logprob/entropy.

        The discrete objective is optimized with REINFORCE in the experiment
        helper, so no differentiable-sort approximation is silently assumed.
        """
        logits = self.forward(features)
        batch = logits.shape[0]
        perms = []
        logps = []
        entropies = []
        for b in range(batch):
            menu = []
            menu_logp = torch.zeros((), device=logits.device)
            menu_entropy = torch.zeros((), device=logits.device)
            for h in range(self.K):
                remaining = list(range(self.m))
                ranking = []
                for _ in range(self.m):
                    local_logits = logits[b, h, remaining]
                    dist = torch.distributions.Categorical(logits=local_logits)
                    local_idx = dist.sample()
                    menu_logp = menu_logp + dist.log_prob(local_idx)
                    menu_entropy = menu_entropy + dist.entropy()
                    chosen = remaining.pop(int(local_idx.item()))
                    ranking.append(chosen)
                menu.append(ranking)
            perms.append(menu)
            logps.append(menu_logp)
            entropies.append(menu_entropy)
        return (
            torch.tensor(perms, dtype=torch.long, device=logits.device),
            torch.stack(logps),
            torch.stack(entropies),
        )

    def parameter_bytes(self) -> int:
        return int(sum(p.numel() * p.element_size() for p in self.parameters()))
