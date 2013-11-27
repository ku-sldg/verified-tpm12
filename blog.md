---
layout: frontpage
title: EECS 662 Blog
---

# EECS 662 Blog

{% for post in site.categories.blog %}
<a href="{{ site.baseurl }}{{ post.url }}">{{ post.title }}</a>

{{ post.content }}

-----

{% endfor %}
