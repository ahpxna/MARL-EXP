#!/usr/bin/env python3
"""DC-Ada's transformation layer (github.com/alqithami/DC-ADA src/agents/transformation.py, read 05/10): residual MLP
encoder obs -> latent, ReLU, LayerNorm(latent), hidden latent -> latent, ReLU, decoder latent -> obs, output + input.  Zero init (the method
default transform_init_std 0.0) = exact identity.  Used by CITY_eval_dca2.py and CITY_w7_dca2_tune.py (PROTOCOL_CITY_WAVE7_20261005)."""
import torch
import torch.nn as nn


class TransformationLayer(nn.Module):
    def __init__(self, obs_dim=7, latent_dim=32):
        super().__init__()
        self.encoder = nn.Linear(obs_dim, latent_dim); self.hidden = nn.Linear(latent_dim, latent_dim); self.decoder = nn.Linear(latent_dim, obs_dim)
        self.layer_norm = nn.LayerNorm(latent_dim)
        for m in (self.encoder, self.hidden, self.decoder):
            nn.init.zeros_(m.weight); nn.init.zeros_(m.bias)

    def forward(self, x):
        latent = torch.relu(self.encoder(x)); latent = self.layer_norm(latent); latent = torch.relu(self.hidden(latent))
        return self.decoder(latent) + x

    def get_params_vector(self):
        return torch.cat([p.data.view(-1) for p in self.parameters()])

    def set_params_vector(self, v):
        i = 0
        for p in self.parameters():
            n = p.numel(); p.data.copy_(v[i:i + n].view(p.shape)); i += n


NPARAM = TransformationLayer().get_params_vector().numel()
