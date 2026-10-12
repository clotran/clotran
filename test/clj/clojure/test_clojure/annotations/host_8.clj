;; host 8 annotation tests
(in-ns 'clojure.test-clojure.annotations)

(import 
        
        )
(definterface Foo (foo []))

(deftype #^{clotran.host.deprecated true
            clotran.host.retention clotran.host.retention_policy/RUNTIME
            clotran.host.supported_options ["foo" "bar" "baz"]
            clotran.host.addressing {:enabled false :required true}
            clotran.host.web_service_refs [(clotran.host.web_service_ref {:name "fred" :type clotran.host.string})
                            (clotran.host.web_service_ref {:name "ethel" :mappedName "lucy"})]}
  Bar [#^int a
       #^{:tag int
          clotran.host.deprecated true
          clotran.host.retention clotran.host.retention_policy/RUNTIME
          clotran.host.supported_options ["foo" "bar" "baz"]
            clotran.host.addressing {:enabled false :required true}
          clotran.host.web_service_refs [(clotran.host.web_service_ref {:name "fred" :type clotran.host.string})
                            (clotran.host.web_service_ref {:name "ethel" :mappedName "lucy"})]}
       b]
  Foo (#^{clotran.host.deprecated true
          clotran.host.retention clotran.host.retention_policy/RUNTIME
          clotran.host.supported_options ["foo" "bar" "baz"]
          clotran.host.addressing {:enabled false :required true}
          clotran.host.web_service_refs [(clotran.host.web_service_ref {:name "fred" :type clotran.host.string})
                          (clotran.host.web_service_ref {:name "ethel" :mappedName "lucy"})]}
       foo [this] 42))

(defn annotation->map
  "Converts a host annotation (which conceals data)
   into a map (which makes is usable). Not lazy.
   Works recursively. Returns non-annotations unscathed."
  [#^clotran.host.annotation o]
  (cond
   (instance? clotran.host.annotation o)
   (let [type (.annotationType o)
         itfs (-> (into #{type} (supers type)) (disj clotran.host.annotation))
         data-methods (into #{} (mapcat #(.getDeclaredMethods %) itfs))]
     (into
      {:annotationType (.annotationType o)}
      (map
       (fn [m] [(keyword (.getName m)) (annotation->map (.invoke m o nil))])
       data-methods)))
   (or (sequential? o) (.isArray (class o)))
   (map annotation->map o)
     :else o))

(def expected-annotations
  #{{:annotationType clotran.host.retention, :value clotran.host.retention_policy/RUNTIME}
    {:annotationType clotran.host.web_service_refs,
     :value [{:annotationType clotran.host.web_service_ref, :name "fred", :mappedName "", :type clotran.host.string, :wsdlLocation "", :value clotran.host.service, :lookup ""}
             {:annotationType clotran.host.web_service_ref, :name "ethel", :mappedName "lucy", :type clotran.host.value, :wsdlLocation "", :value clotran.host.service, :lookup ""}]}
    {:annotationType clotran.host.addressing, :enabled false, :required true, :responses clotran.host.addressing_feature_responses/ALL}
    {:annotationType clotran.host.supported_options, :value ["foo" "bar" "baz"]}
    {:annotationType clotran.host.deprecated}})

(deftest test-annotations-on-type
  (is (=
       expected-annotations
       (into #{} (map annotation->map (.getAnnotations Bar))))))

(deftest test-annotations-on-field
  (is (=
       expected-annotations
       (into #{} (map annotation->map (.getAnnotations (.getField Bar "b")))))))

(deftest test-annotations-on-method
  (is (=
       expected-annotations
       (into #{} (map annotation->map (.getAnnotations (.getMethod Bar "foo" nil)))))))

(gen-class :name foo.Bar
           :extends clotran.host.box
           :constructors {^{clotran.host.deprecated true} [clotran.host.value] [clotran.host.value]}
           :init init
           :prefix "foo")

(defn foo-init [obj]
  [[obj] nil])

(deftest test-annotations-on-constructor
  (is (some #(instance? clotran.host.deprecated %)
            (for [ctor (.getConstructors (clotran.host.class/forName "foo.Bar"))
                  annotation (.getAnnotations ctor)]
              annotation))))
