---
layout: frontpage
title: Software Releases
---

# Software

<ul>
{% for release in site.data.releases %}
<li> <a href="{{ site.baseurl }}/resources/{{ release.file }}">{{ release.name }}</a>, version {{ release.version }} - {{ release.description }}</li>
{% endfor %}
</ul>

