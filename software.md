---
layout: frontpage
title: Software Releases
---

# Software and Model Releases

<ul>
{% for release in site.data.releases %}
<li> <a href="{{ site.baseurl }}/{{ site.repo }}/resources/{{ release.file }}">{{ release.name }}</a>, version {{ release.version }} - {{ release.description }}</li>
{% endfor %}
</ul>

Visit {{ site.maintitle }} on [github](http://github.com/{{ site.account }}/{{ site.repo }})
