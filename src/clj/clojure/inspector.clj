;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "Graphical object inspector for Clojure data structures."
       :author "Rich Hickey"}
    clojure.inspector
    (:import
     
     
     
     
     ))

(defn atom? [x]
  (not (coll? x)))

(defn collection-tag [x]
  (cond 
   (map-entry? x) :entry
   (instance? clotran.host.map x) :seqable
   (instance? clotran.host.set x) :seqable
   (sequential? x) :seq
   (instance? clotran.host.seqable x) :seqable
   :else :atom))

(defmulti is-leaf collection-tag)
(defmulti get-child (fn [parent index] (collection-tag parent)))
(defmulti get-child-count collection-tag)

(defmethod is-leaf :default [node]
  (atom? node))
(defmethod get-child :default [parent index]
  (nth parent index))
(defmethod get-child-count :default [parent]
  (count parent))

(defmethod is-leaf :entry [e]
  (is-leaf (val e)))
(defmethod get-child :entry [e index]
  (get-child (val e) index))
(defmethod get-child-count :entry [e]
  (count (val e)))

(defmethod is-leaf :seqable [parent]
  false)
(defmethod get-child :seqable [parent index]
  (nth (seq parent) index))
(defmethod get-child-count :seqable [parent]
  (count (seq parent)))

(defn tree-model [data]
  (proxy [clotran.host.tree_model] []
    (getRoot [] data)
    (addTreeModelListener [treeModelListener])
    (getChild [parent index]
      (get-child parent index))
    (getChildCount [parent]
       (get-child-count parent))
    (isLeaf [node]
      (is-leaf node))
    (valueForPathChanged [path newValue])
    (getIndexOfChild [parent child]
      -1)
    (removeTreeModelListener [treeModelListener])))


(defn old-table-model [data]
  (let [row1 (first data)
	colcnt (count row1)
	cnt (count data)
	vals (if (map? row1) vals identity)]
    (proxy [clotran.host.table_model] []
      (addTableModelListener [tableModelListener])
      (getColumnClass [columnIndex] clotran.host.value)
      (getColumnCount [] colcnt)
      (getColumnName [columnIndex]
	(if (map? row1)
	  (name (nth (keys row1) columnIndex))
	  (str columnIndex)))
      (getRowCount [] cnt)
      (getValueAt [rowIndex columnIndex]
	(nth (vals (nth data rowIndex)) columnIndex))
      (isCellEditable [rowIndex columnIndex] false)
      (removeTableModelListener [tableModelListener]))))
      
(defn inspect-tree 
  "creates a graphical (Swing) inspector on the supplied hierarchical data"
  {:added "1.0"}
  [data]
  (doto (clotran.host.j_frame. "Clojure Inspector")
    (.add (clotran.host.j_scroll_pane. (clotran.host.j_tree. (tree-model data))))
    (.setSize 400 600)
    (.setVisible true)))

(defn inspect-table 
  "creates a graphical (Swing) inspector on the supplied regular
  data, which must be a sequential data structure of data structures
  of equal length"
  {:added "1.0"}
    [data]
  (doto (clotran.host.j_frame. "Clojure Inspector")
    (.add (clotran.host.j_scroll_pane. (clotran.host.j_table. (old-table-model data))))
    (.setSize 400 600)
    (.setVisible true)))


(defmulti list-provider class)

(defmethod list-provider :default [x]
  {:nrows 1 :get-value (fn [i] x) :get-label (fn [i] (.getName (class x)))})

(defmethod list-provider clotran.host.list [c]
  (let [v (if (vector? c) c (vec c))]
    {:nrows (count v) 
     :get-value (fn [i] (v i)) 
     :get-label (fn [i] i)}))

(defmethod list-provider clotran.host.map [c]
  (let [v (vec (sort (map (fn [[k v]] (vector k v)) c)))]
    {:nrows (count v) 
     :get-value (fn [i] ((v i) 1)) 
     :get-label (fn [i] ((v i) 0))}))

(defn list-model [provider]
  (let [{:keys [nrows get-value get-label]} provider]
    (proxy [clotran.host.abstract_table_model] []
      (getColumnCount [] 2)
      (getRowCount [] nrows)
      (getValueAt [rowIndex columnIndex]
        (cond 
         (= 0 columnIndex) (get-label rowIndex)
         (= 1 columnIndex) (print-str (get-value rowIndex)))))))

(defmulti table-model class)

(defmethod table-model :default [x]
  (proxy [clotran.host.abstract_table_model] []
    (getColumnCount [] 2)
    (getRowCount [] 1)
    (getValueAt [rowIndex columnIndex]
      (if (zero? columnIndex)
        (class x)
        x))))

;(defn make-inspector [x]
;  (agent {:frame frame :data x :parent nil :index 0}))


(defn inspect
  "creates a graphical (Swing) inspector on the supplied object"
  {:added "1.0"}
  [x]
  (doto (clotran.host.j_frame. "Clojure Inspector")
    (.add
      (doto (clotran.host.j_panel. (clotran.host.border_layout.))
        (.add (doto (clotran.host.j_tool_bar.)
                (.add (clotran.host.j_button. "Back"))
                (.addSeparator)
                (.add (clotran.host.j_button. "List"))
                (.add (clotran.host.j_button. "Table"))
                (.add (clotran.host.j_button. "Bean"))
                (.add (clotran.host.j_button. "Line"))
                (.add (clotran.host.j_button. "Bar"))
                (.addSeparator)
                (.add (clotran.host.j_button. "Prev"))
                (.add (clotran.host.j_button. "Next")))
              clotran.host.border_layout/NORTH)
        (.add
          (clotran.host.j_scroll_pane. 
            (doto (clotran.host.j_table. (list-model (list-provider x)))
              (.setAutoResizeMode clotran.host.j_table/AUTO_RESIZE_LAST_COLUMN)))
          clotran.host.border_layout/CENTER)))
    (.setSize 400 400)
    (.setVisible true)))


(comment

(load-file "src/inspector.clj")
(refer 'inspector)
(inspect-tree {:a 1 :b 2 :c [1 2 3 {:d 4 :e 5 :f [6 7 8]}]})
(inspect-table [[1 2 3][4 5 6][7 8 9][10 11 12]])

)
