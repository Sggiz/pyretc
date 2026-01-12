
print(empty == empty)
print(empty <> empty)
print(empty == link(1, empty))
print(empty <> link(1, empty))
print("\n")
print(link(1, empty) == link(1, empty))
print(link(1, empty) <> link(1, empty))
print(link(1, empty) == link(2, empty))
print(link(1, empty) <> link(2, empty))
print(link(1, empty) == link(2, link(3, empty)))
print(link(1, empty) <> link(2, link(3, empty)))

print("\n")



