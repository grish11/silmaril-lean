(in-package "ACL2")

(include-book "acl2-definitions")

(defthm silmaril-first-of-cons
  (equal (silmaril-first (cons head tail)) head)
  :rule-classes nil)

(defthm silmaril-first-of-singleton
  (equal (silmaril-first (cons item nil)) item)
  :rule-classes nil)
