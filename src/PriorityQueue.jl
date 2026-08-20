"A cached minimum priority, with `nothing` representing the monoid identity."
struct _PrioritySummary{P}
    priority::Union{Nothing,P}
end

struct _PriorityMeasure{P} <: Measure end
Base.identity(::_PriorityMeasure{P}) where {P} = _PrioritySummary{P}(nothing)
measure(::_PriorityMeasure{P}, entry::Pair) where {P} =
    _PrioritySummary{P}(convert(P, last(entry)))

function combine(::_PriorityMeasure{P}, left::_PrioritySummary{P}, right::_PrioritySummary{P}) where {P}
    isnothing(left.priority) && return right
    isnothing(right.priority) && return left
    isless(something(right.priority), something(left.priority)) ? right : left
end

const _PriorityTree{T,P} = MeasuredFingerTree{
    Pair{T,P},
    _PriorityMeasure{P},
    _PrioritySummary{P},
}

"""A persistent, stable min-priority queue."""
struct PriorityQueue{T,P}
    tree::_PriorityTree{T,P}
end

PriorityQueue(::Type{T}, ::Type{P}) where {T,P} =
    PriorityQueue{T,P}(MeasuredFingerTree(Pair{T,P}, _PriorityMeasure{P}()))
PriorityQueue{T,P}() where {T,P} = PriorityQueue(T, P)

function PriorityQueue(::Type{T}, ::Type{P}, entries) where {T,P}
    queue = PriorityQueue(T, P)
    for entry in entries
        queue = enqueue(queue, first(entry), last(entry))
    end
    queue
end

PriorityQueue(entries) = _priority_queue(entries, eltype(entries))
_priority_queue(entries, ::Type{<:Pair{T,P}}) where {T,P} = PriorityQueue(T, P, entries)
_priority_queue(_, type) = throw(ArgumentError("priority queue entries must be Pair values, got $type"))

Base.eltype(::Type{<:PriorityQueue{T,P}}) where {T,P} = Pair{T,P}
Base.eltype(::PriorityQueue{T,P}) where {T,P} = Pair{T,P}
Base.IteratorEltype(::Type{<:PriorityQueue}) = Base.HasEltype()
Base.IteratorSize(::Type{<:PriorityQueue}) = Base.HasLength()
Base.length(queue::PriorityQueue) = length(queue.tree)
Base.isempty(queue::PriorityQueue) = isempty(queue.tree)
Base.copy(queue::PriorityQueue) = queue
Base.empty(::PriorityQueue{T,P}) where {T,P} = PriorityQueue(T, P)
Base.first(queue::PriorityQueue) = peek(queue)

"Return a new queue containing `value` at `priority`."
function enqueue(queue::PriorityQueue{T,P}, value, priority) where {T,P}
    entry = convert(T, value) => convert(P, priority)
    PriorityQueue{T,P}(conjr(queue.tree, entry))
end
enqueue(queue::PriorityQueue, entry::Pair) = enqueue(queue, first(entry), last(entry))

struct _ContainsPriority{P}
    priority::P
end
function (predicate::_ContainsPriority)(summary::_PrioritySummary)
    !isnothing(summary.priority) && isequal(something(summary.priority), predicate.priority)
end

function _minimum_predicate(queue::PriorityQueue{T,P}) where {T,P}
    isempty(queue) && throw(BoundsError(queue))
    summary = measure(queue.tree)
    _ContainsPriority{P}(something(summary.priority))
end

"Return the earliest entry having minimum priority."
function Base.peek(queue::PriorityQueue{T,P})::Pair{T,P} where {T,P}
    predicate = _minimum_predicate(queue)
    prefix = Base.identity(queue.tree.measureop)
    index = _find_measure(queue.tree.measureop, predicate, queue.tree.root, prefix, 0)
    queue.tree[index]
end

"Return the minimum priority without removing its entry."
peekpriority(queue::PriorityQueue) = last(peek(queue))

"Return `(entry, remaining_queue)` without modifying `queue`."
function dequeue(queue::PriorityQueue{T,P}) where {T,P}
    predicate = _minimum_predicate(queue)
    left, entry, right = split_measure(predicate, queue.tree)
    entry, PriorityQueue{T,P}(concat(left, right))
end

function Base.iterate(queue::PriorityQueue)
    isempty(queue) && return nothing
    entry, rest = dequeue(queue)
    entry, rest
end
Base.iterate(::PriorityQueue, state::PriorityQueue) = iterate(state)

Base.:(==)(left::PriorityQueue, right::PriorityQueue) = left.tree == right.tree

function Base.show(io::IO, queue::PriorityQueue{T,P}) where {T,P}
    print(io, "PriorityQueue{")
    show(io, T)
    print(io, ", ")
    show(io, P)
    print(io, "}(", length(queue), " entries)")
end
