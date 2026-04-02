
default:
	lake build

doc:
	cd docbuild && lake -Kenv=dev build GL:docs