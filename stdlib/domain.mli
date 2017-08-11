type 'a t
(** A domain of type ['a t] runs independently, eventually producing a
    result of type 'a, or an exception *)

val spawn : (unit -> 'a) -> 'a t
(** [spawn f] creates a new domain that runs in parallel with the
    current domain. *)

val join : 'a t -> 'a
(** [join d] blocks until domain [d] runs to completion.
    If [d] results in a value, then that is returned by [join d].
    If [d] raises an uncaught exception, then that is thrown by [join d].
    Domains may only be joined once: subsequent uses of [join d]
    raise Invalid_argument. *)

type id = private int
(** Domains have unique integer identifiers *)

val get_id : 'a t -> id

val self : unit -> id
(** [self ()] is the identifier of the currently running domain *)


module Sync : sig
  (** Low-level synchronisation primitives.

      The general usage pattern for these primitives is to test a
      predicate of atomic variables in a critical section and call
      [wait] if the predicate does not hold. The domain that causes
      the predicate to become true must then call [notify].

      For example, here one domain waits for another to complete work:

          let done = Atomic.make false

          let rec await_completion () =
            let success =
              critical_section (fun () ->
                if Atomic.get done then true else (wait (); false)) in
            if success then () else await_completion ()

          let signal_completion waiting_domain =
            Atomic.set success true;
            notify waiting_domain

      Semantically, the primitives are similar to having a single
      monitor (or mutex + condition variable) per domain. That is,
      [critical_section f] acquires the current domain's mutex and
      runs [f], [wait ()] waits on the current domain's condition
      variable (releasing the mutex during the wait), and [notify d]
      acquires domain [d]'s mutex and signals its condition variable.
      The only difference from standard monitors is that [notify d]
      waits for any in-progress critical section to complete.

      However, the actual implementation is somewhat different. In
      particular, [critical_section f] is cheaper than acquiring a mutex,
      and performs no more atomic operations than [f] does. *)

  val critical_section : (unit -> 'a) -> 'a
  (** [critical_section f] runs [f], but blocks notifications until
      [f] returns. See [notify] below. *)

  val notify : id -> unit
  (** If the domain [d] is within a critical section (i.e. is evaluating
      [critical_section f]), then [notify d] marks this critical section
      as "notified" (causing any call to [wait] to return, see below),
      and waits for the critical section to complete before returning.
      If [d] is not in a critical section, then [notify d] does nothing. *)


  val wait : unit -> unit
  (** [wait] must be called from within a critical section, and returns
      only when that critical section is notified by a call to [notify].
      It does not matter whether [notify] is called before or after
      [wait] begins: it is the critical section that is being notified,
      not the call to wait. If wait is called and finds that the current
      critical has already been notified, it returns immediately.

      Calling [wait ()] twice within the same critical section is not
      useful: the first call to [wait ()] returns when the critical
      section is notified, so the second call to [wait] will always
      return immediately, as the critical section is already notified. *)
end

module BVar : sig
  (* A bvar is a reference, either empty or full,
     supporting atomic "take" and "put" operations.

     These are biased towards one domain. So, take
     and put operations by the same domain will be
     fast, while contended operations will be very
     slow. *)
  type 'a t

  (* Create an (initially full) bvar *)
  external create : 'a -> 'a t = "caml_bvar_create"

  (* Remove the value from a bvar, leaving it empty.
     Raises Not_found if the bvar is already empty.
     If several domains concurrently attempt to take,
     exactly one of them will succeed *)
  external take : 'a t -> 'a = "caml_bvar_take"

  (* Put a value into an empty bvar, leaving it full.
     Raises Invalid_argument if the bvar is already full.
     If several domains concurrently attempt to put,
     exactly one of them will succeed *)
  external put : 'a t -> 'a -> unit = "caml_bvar_put"

  (* Check whether a bvar is empty. Being nonempty/empty is
     no guarantee that a take/put will succeed: an intervening
     take/put may occur *)
  external is_empty : 'a t -> bool = "caml_bvar_is_empty"
end
