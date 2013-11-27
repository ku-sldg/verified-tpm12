---
layout: frontpage
title: Verified TPM
---

The goal of the Verified TPM is specifying and verifying the TPM 1.2 formally in
PVS.  We specify the TPM as a state transformation system with each
instruction modifying the TPM state.  We then use a state monad to
sequence instruction execution, threading state through a sequence of
instructions.

## Recent Activities

<ul>
{% for activity in site.data.activities %}
<li>{{ activity.description }}</li>
{% endfor %}
</ul>

## Team

Verified TPM is run by the [System-Level Design Group](http://ku-sldg.github.io)
in The Information and Telecommunication Technology Center at The
University of Kansas.

### Faculty

* Perry Alexander (PI)

### Students

* Brigid Halling

## Sponsors

Verified TPM is sponsored by The Battelle Memorial Trust
