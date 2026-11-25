import Cjr

#print axioms Cjr.baseStep_deterministic
#print axioms Cjr.step_deterministic
#print axioms Cjr.decompose_fill
#print axioms Cjr.step_contextual
#print axioms Cjr.baseStep_nonvalue
#print axioms Cjr.decompose_fillItem
#print axioms Cjr.run_done_contextual
#print axioms Cjr.run_done_steps
#print axioms Cjr.stateInit_wf
#print axioms Cjr.stack_fresh
#print axioms Cjr.raw_fresh
#print axioms Cjr.block_fresh
#print axioms Cjr.obj_fresh
#print axioms Cjr.Examples.factorial_five

#print axioms Cjr.Cangjie.emit_metadata_checked

-- Compositional execution and linked-list proofs.
#print axioms Cjr.step_under
#print axioms Cjr.steps_run
#print axioms Cjr.evaluates_unique
#print axioms Cjr.LinkedList.represents_unique
#print axioms Cjr.LinkedList.node_extends
#print axioms Cjr.LinkedList.head_correct
#print axioms Cjr.LinkedList.tail_correct
#print axioms Cjr.LinkedList.isEmpty_correct
#print axioms Cjr.LinkedList.length_correct
#print axioms Cjr.LinkedList.append_correct
#print axioms Cjr.LinkedList.reverseAux_correct
#print axioms Cjr.LinkedList.reverse_correct
#print axioms Cjr.LinkedList.ofList_correct
#print axioms Cjr.LinkedList.consCall_correct
#print axioms Cjr.LinkedList.reverseCall_correct
#print axioms Cjr.LinkedList.models_append
#print axioms Cjr.LinkedList.models_reverse
#print axioms Cjr.LinkedList.append_empty_left
#print axioms Cjr.LinkedList.append_empty_right
#print axioms Cjr.LinkedList.append_associative
#print axioms Cjr.LinkedList.reverse_empty
#print axioms Cjr.LinkedList.reverse_involutive
#print axioms Cjr.LinkedList.reverse_append
#print axioms Cjr.LinkedList.reverse_cons
#print axioms Cjr.LinkedList.length_empty
#print axioms Cjr.LinkedList.length_cons
#print axioms Cjr.LinkedList.length_append
#print axioms Cjr.LinkedList.length_reverse
#print axioms Cjr.LinkedList.head_cons
#print axioms Cjr.LinkedList.tail_cons
#print axioms Cjr.LinkedList.models_terminate
#print axioms Cjr.LinkedList.models_all_results
#print axioms Cjr.LinkedList.models_no_stuck

-- Stateful iterator: real object-store steps, frames, traversal and exhaustion.
#print axioms Cjr.Evaluates.field_store
#print axioms Cjr.LinkedList.Iterator.Protected.advance
#print axioms Cjr.LinkedList.Iterator.created_rep
#print axioms Cjr.LinkedList.Iterator.advance_bounded
#print axioms Cjr.LinkedList.Iterator.create_correct
#print axioms Cjr.LinkedList.Iterator.next_some
#print axioms Cjr.LinkedList.Iterator.next_none
#print axioms Cjr.LinkedList.Iterator.exhausted_repeat
#print axioms Cjr.LinkedList.Iterator.iterate_correct
#print axioms Cjr.LinkedList.Iterator.iterate_exhausted
#print axioms Cjr.LinkedList.Iterator.next_terminates

-- Mathematical sorting and operational mergesort refinement.
#print axioms Cjr.LinkedList.MergeSort.deal_lengths
#print axioms Cjr.LinkedList.MergeSort.deal_smaller
#print axioms Cjr.LinkedList.MergeSort.deal_perm
#print axioms Cjr.LinkedList.MergeSort.merge_perm
#print axioms Cjr.LinkedList.MergeSort.merge_ordered
#print axioms Cjr.LinkedList.MergeSort.Sorting.count_eq
#print axioms Cjr.LinkedList.MergeSort.split_correct
#print axioms Cjr.LinkedList.MergeSort.merge_correct
#print axioms Cjr.LinkedList.MergeSort.sort_correct
#print axioms Cjr.LinkedList.MergeSort.sortExpr_correct
#print axioms Cjr.LinkedList.MergeSort.sort_all_results
#print axioms Cjr.LinkedList.MergeSort.sort_terminates
#print axioms Cjr.LinkedList.MergeSort.sort_no_stuck

-- Exact small-step accounting and logarithmic mergesort bounds.
#print axioms Cjr.exec_unique
#print axioms Cjr.Exec.run
#print axioms Cjr.LinkedList.MergeSort.sorted_spec
#print axioms Cjr.LinkedList.MergeSort.split_counted
#print axioms Cjr.LinkedList.MergeSort.merge_counted
#print axioms Cjr.LinkedList.MergeSort.sort_counted
#print axioms Cjr.LinkedList.MergeSort.ceilLog_le_iff
#print axioms Cjr.LinkedList.MergeSort.upper_height
#print axioms Cjr.LinkedList.MergeSort.lower_height
#print axioms Cjr.LinkedList.MergeSort.sortSteps_bounds
#print axioms Cjr.LinkedList.MergeSort.operational_bound
#print axioms Cjr.LinkedList.MergeSort.every_execution_bound
#print axioms Cjr.LinkedList.MergeSort.theta_n_log2
#print axioms Cjr.LinkedList.MergeSort.execution_theta
#print axioms Cjr.LinkedList.MergeSort.budget_suffices
