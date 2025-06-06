(*
 * TINY (Tiny Is Not Yasa (Yet Another Static Analyzer)):
 * a simple abstract interpreter for teaching purpose.
 * Copyright (C) 2012  P. Roux
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

(** Various utility functions. *)

val lines_of_string : string -> int
(** Returns the number of '\n' appearing in a string. *)

val output_filename_string : string option -> string
(** Returns string in option or "stdout" if None given. *)

val with_out_ch : string option -> (out_channel -> 'b) -> 'b
(** Open an output channel on given filename, gives it to the given function and
    eventually closes the channel. stdout is used if no filename is given. *)

val with_in_ch : string option -> (in_channel -> 'b) -> 'b
(** Same as [with_out_ch] for input channels (with stdin instead of stdout). *)
