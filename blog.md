---
layout: frontpage
title: {{ site.title }}
---

# Blog

{% for post in site.categories.blog %}

<a href="{{ site.baseurl }}{{ post.url }}">{{ post.title }}</a>

{{ post.date | date_to_string }}

{{ post.content }}

-----

{% endfor %}
