---
layout: frontpage
title: Publications
---

# Publications

<ul>
{% for paper in site.data.publications %}
<li>{{ paper.author }}, <a href="{{ site.baseurl }}/resources/{{ paper.pdf }}">{{ paper.title }}</a>, {{ paper.where }}</li>
{% endfor %}
</ul>
