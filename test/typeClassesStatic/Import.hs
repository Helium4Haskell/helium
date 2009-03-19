import ImportTest.Imported

class ClassA a

-- Sadly this test fails because imported modules containing classes cannot be compiled correctly.
-- Currently this test will fail because of a translation error from core to lvm whereas it should fail due to a duplicate class definition from an import


  
