.. _tac_triv:

triv
====

Summary
-------

The ``triv`` tactic proves ``⊢ True``.

It also proves goals of the form ``x = x`` and more generally of the form ``x = y`` when ``x`` and ``y`` are definitionally equal, but traditionally people use ``rfl`` to do that.

Examples
--------

If your goal is

.. code-block::

   ⊢ True

then it's pretty triv, so try ``triv``.

Details
-------

Note that ``True`` here is the true proposition. If you know a proof in your head that the goal is true, that's not good enough. If your goal is ``⊢ P`` and you can tell that ``P`` is true (e.g. because you can deduce it from the hypotheses), ``triv`` won't work; ``triv`` only works when the goal is actually definitionally equal to ``True``. 

Further notes
-------------

The ``constructor`` tactic also proves a ``True`` goal, although you would have to learn a bit about inductive types to understand why.



